"""Pinned campaign state, immutable experiments, and experiment lineage."""

import asyncio
import fcntl
import hashlib
import json
import logging
import os
import platform
import re
import shutil
import sqlite3
import subprocess
import uuid
from contextlib import contextmanager
from pathlib import Path

from .artifacts import contained, now, read_json, sha256, write_json
from .models import CampaignConfig, ExperimentConfig, RunAction, resolve_patch
from .runner import execute_run
from .scheduler import Scheduler
from .source_access import SourceAccess
from .summarizer import ranking_key, summarize_run


def source_manifest(root: Path) -> dict[str, str]:
    names = subprocess.check_output(
        [
            "git",
            "ls-files",
            "--cached",
            "--others",
            "--exclude-standard",
            "--",
            "src",
            "smt2parser/src",
            "to_vmt",
            "Cargo.toml",
            "Cargo.lock",
            "README.md",
        ],
        cwd=root,
        text=True,
    ).splitlines()
    names += [".cargo/config.toml"] if (root / ".cargo/config.toml").exists() else []
    return {
        name: sha256(contained(root, name))
        for name in sorted(set(names))
        if (root / name).is_file()
        and (Path(name).suffix in {".rs", ".md", ".toml"} or name == "Cargo.lock")
    }


def create_campaign(root: Path, output: Path, config: CampaignConfig, binary: Path | None = None):
    root, output = root.resolve(), output.resolve()
    benchmarks = []
    for raw in config.benchmarks:
        path = contained(root, raw)
        if not path.is_file() or path.suffix != ".vmt":
            raise ValueError(f"Expected a VMT benchmark in the checkout: {raw}")
        name = path.relative_to(root).as_posix()
        slug = re.sub(r"[^a-zA-Z0-9_-]+", "-", path.stem).strip("-")[:60] or "benchmark"
        identifier = slug + "-" + hashlib.sha256(name.encode()).hexdigest()[:8]
        benchmarks.append({"benchmark_id": identifier, "path": name, "sha256": sha256(path)})
    if len({b["path"] for b in benchmarks}) != len(benchmarks):
        raise ValueError("Benchmark paths resolve to duplicates")
    output.mkdir(parents=True, exist_ok=False)
    before = source_manifest(root)
    if binary is None:
        with (output / "build.log").open("wb") as log:
            subprocess.run(
                ["cargo", "build", "--release", "-p", "yardbird"],
                cwd=root,
                stdout=log,
                stderr=subprocess.STDOUT,
                check=True,
            )
        binary = root / "target/release/yardbird"
    binary = binary.resolve()
    if source_manifest(root) != before:
        raise ValueError("Source changed while building; start a fresh campaign")
    context = output / "context"
    context.mkdir()
    pinned = context / "yardbird"
    shutil.copy2(binary, pinned)
    pinned.chmod(0o555)
    for path in Path(__file__).with_name("context").glob("*.md"):
        shutil.copyfile(path, context / path.name)
    ranker_hash = None
    if config.ranker_model:
        ranker = contained(root, config.ranker_model)
        shutil.copyfile(ranker, context / "ranker-model.json")
        ranker_hash = sha256(ranker)
    try:
        z3_version = subprocess.check_output(["z3", "--version"], text=True).strip()
    except (OSError, subprocess.CalledProcessError):
        z3_version = None
    manifest = {
        "schema_version": 1,
        "created_at": now(),
        "source_root": str(root),
        "git_sha": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip(),
        "source_files": before,
        "binary_sha256": sha256(pinned),
        "ranker_sha256": ranker_hash,
        "build_mode": "provided_binary" if not (output / "build.log").exists() else "cargo_release",
        "host": platform.node(),
        "platform": platform.platform(),
        "z3_cli_version": z3_version,
        "z3_runtime_version": "Recorded per run from Yardbird stderr",
        "build_environment": {
            k: os.environ.get(k) for k in ("RUSTFLAGS", "CARGO_BUILD_TARGET", "RUSTC")
        },
        "config": config.model_dump(),
        "benchmarks": benchmarks,
    }
    write_json(output / "campaign.json", manifest)
    with sqlite3.connect(output / "campaign.sqlite") as db:
        db.executescript("""
          PRAGMA foreign_keys=ON;
          CREATE TABLE benchmarks (benchmark_id TEXT PRIMARY KEY, path TEXT NOT NULL,
                                   status TEXT NOT NULL DEFAULT 'pending', error TEXT);
          CREATE TABLE runs (run_id TEXT PRIMARY KEY, benchmark_id TEXT NOT NULL REFERENCES benchmarks,
            ordinal INTEGER NOT NULL, parent_run_id TEXT REFERENCES runs, state TEXT NOT NULL,
            config_json TEXT NOT NULL, action_json TEXT NOT NULL, started_at TEXT, finished_at TEXT,
            termination_reason TEXT, wall_time REAL, completed_depth INTEGER, current_depth INTEGER,
            current_refinement_step INTEGER, solver_time REAL, profile_path TEXT, summary_path TEXT,
            UNIQUE(benchmark_id, ordinal));
          CREATE TABLE events (event_id INTEGER PRIMARY KEY, benchmark_id TEXT NOT NULL,
                               created_at TEXT NOT NULL, event_json TEXT NOT NULL);
          CREATE VIEW experiments AS SELECT runs.*,
            json_extract(config_json, '$.strategy') AS strategy,
            json_extract(config_json, '$.cost_function') AS cost_function,
            json_extract(config_json, '$.egraph_builder') AS egraph_builder,
            json_extract(config_json, '$.candidate_winners_per_group') AS candidate_winners_per_group,
            json_extract(config_json, '$.instantiation_ranker') AS instantiation_ranker,
            json_extract(config_json, '$.property_check_mode') AS property_check_mode,
            json_extract(action_json, '$.hypothesis') AS hypothesis,
            json_extract(action_json, '$.expected_signal') AS expected_signal,
            json_extract(action_json, '$.rationale') AS rationale FROM runs;
        """)
        for item in benchmarks:
            db.execute(
                "INSERT INTO benchmarks(benchmark_id,path) VALUES (?,?)",
                (item["benchmark_id"], item["path"]),
            )
            directory = output / "benchmarks" / item["benchmark_id"]
            directory.mkdir(parents=True)
            write_json(directory / "benchmark.json", item)
    return Campaign(output)


class Campaign:
    def __init__(self, directory: Path):
        self.directory = directory.resolve()
        self.manifest = read_json(self.directory / "campaign.json")
        self.config = CampaignConfig.model_validate(self.manifest["config"])
        self.root = Path(self.manifest["source_root"])
        self.source = SourceAccess(self.root, self.manifest["source_files"])
        self.benchmarks = {b["benchmark_id"]: b for b in self.manifest["benchmarks"]}
        self.scheduler = Scheduler(self.config.scheduler.max_parallel_runs)
        self.agent_slots = asyncio.Semaphore(self.config.scheduler.max_parallel_agents)

    @contextmanager
    def lock(self):
        with (self.directory / ".campaign.lock").open("a") as stream:
            try:
                fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as exc:
                raise ValueError("Another process is operating this campaign") from exc
            try:
                self.verify_pins()
                yield
            finally:
                fcntl.flock(stream, fcntl.LOCK_UN)

    @contextmanager
    def db(self):
        with sqlite3.connect(self.directory / "campaign.sqlite") as db:
            db.row_factory = sqlite3.Row
            db.execute("PRAGMA foreign_keys=ON")
            yield db

    def verify_pins(self):
        if source_manifest(self.root) != self.manifest["source_files"]:
            raise ValueError("Pinned source changed; create a new campaign")
        if sha256(self.directory / "context/yardbird") != self.manifest["binary_sha256"]:
            raise ValueError("Pinned binary changed")
        if (
            self.manifest["ranker_sha256"]
            and sha256(self.directory / "context/ranker-model.json")
            != self.manifest["ranker_sha256"]
        ):
            raise ValueError("Pinned ranker model changed")
        for benchmark in self.benchmarks.values():
            if sha256(contained(self.root, benchmark["path"])) != benchmark["sha256"]:
                raise ValueError("Pinned benchmark changed")

    def runs(self, benchmark_id: str) -> list[dict]:
        if benchmark_id not in self.benchmarks:
            raise ValueError("Unknown benchmark")
        with self.db() as db:
            return [
                dict(r)
                for r in db.execute(
                    "SELECT * FROM runs WHERE benchmark_id=? ORDER BY ordinal", (benchmark_id,)
                )
            ]

    def run_directory(self, run_id: str, benchmark_id: str | None = None) -> Path:
        with self.db() as db:
            row = db.execute("SELECT * FROM runs WHERE run_id=?", (run_id,)).fetchone()
        if row is None or (benchmark_id and row["benchmark_id"] != benchmark_id):
            raise ValueError("Unknown run or run belongs to another benchmark")
        return self.directory / "benchmarks" / row["benchmark_id"] / "runs" / row["run_id"]

    def summaries(self, benchmark_id: str):
        return [
            (row, read_json(self.run_directory(row["run_id"]) / "summary.json"))
            for row in self.runs(benchmark_id)
            if row["state"] == "finished"
        ]

    def status(self, benchmark_id: str, state: str, error: str | None = None):
        with self.db() as db:
            db.execute(
                "UPDATE benchmarks SET status=?,error=? WHERE benchmark_id=?",
                (state, error, benchmark_id),
            )

    def event(self, benchmark_id: str, value: dict):
        record = {"created_at": now(), **value}
        encoded = json.dumps(record, sort_keys=True)
        with self.db() as db:
            db.execute(
                "INSERT INTO events(benchmark_id,created_at,event_json) VALUES(?,?,?)",
                (benchmark_id, record["created_at"], encoded),
            )
        with (self.directory / "benchmarks" / benchmark_id / "agent-events.jsonl").open(
            "a"
        ) as stream:
            stream.write(encoded + "\n")

    async def run(self, benchmark_id: str, action: RunAction | None = None) -> dict:
        async def operation():
            return await self._run(benchmark_id, action)

        return await self.scheduler.run(benchmark_id, operation)

    async def _run(self, benchmark_id: str, action: RunAction | None):
        rows = self.runs(benchmark_id)
        if any(r["termination_reason"] == "spawn_error" for r in rows):
            raise RuntimeError(
                "A prior attempt could not spawn Yardbird; start a new campaign after fixing the executable"
            )
        if any(r["state"] != "finished" for r in rows):
            raise RuntimeError("Campaign has an unfinished attempt; inspect it before continuing")
        if len(rows) >= self.config.executions_per_benchmark:
            raise ValueError("Execution budget exhausted")
        ordinal = len(rows) + 1
        if ordinal <= 2:
            if action is not None:
                raise ValueError("Runs 1 and 2 are mandatory baseline and concrete reference")
            config = (
                ExperimentConfig()
                if ordinal == 1
                else ExperimentConfig(strategy="concrete", cost_function="bmc-cost")
            )
        else:
            if action is None:
                raise ValueError(
                    "Adaptive runs require parent, patch, hypothesis and expected signal"
                )
            parent = next((r for r in rows if r["run_id"] == action.parent_run_id), None)
            if parent is None:
                raise ValueError("Parent must be a completed run of this benchmark")
            config = resolve_patch(
                ExperimentConfig.model_validate_json(parent["config_json"]),
                action.config_patch,
                self.config.ranker_model is not None,
            )
        try:
            self.verify_pins()
        except ValueError as exc:
            raise RuntimeError(str(exc)) from exc
        run_id = f"{benchmark_id}-r{ordinal:02d}-{uuid.uuid4().hex[:8]}"
        parent_id = action.parent_run_id if action else None
        action_data = (
            action.model_dump()
            if action
            else {"action": "MANDATORY", "kind": "baseline" if ordinal == 1 else "concrete"}
        )
        with self.db() as db:
            db.execute(
                "INSERT INTO runs(run_id,benchmark_id,ordinal,parent_run_id,state,config_json,action_json) VALUES(?,?,?,?,?,?,?)",
                (
                    run_id,
                    benchmark_id,
                    ordinal,
                    parent_id,
                    "running",
                    config.model_dump_json(),
                    json.dumps(action_data),
                ),
            )
        logging.getLogger(__name__).info(
            "%s run %d/%d started (%s)",
            benchmark_id,
            ordinal,
            self.config.executions_per_benchmark,
            config.strategy,
        )
        directory = self.run_directory(run_id)
        benchmark = self.benchmarks[benchmark_id]
        metadata = await execute_run(
            directory=directory,
            run_id=run_id,
            benchmark_id=benchmark_id,
            ordinal=ordinal,
            binary=self.directory / "context/yardbird",
            binary_hash=self.manifest["binary_sha256"],
            benchmark=contained(self.root, benchmark["path"]),
            benchmark_hash=benchmark["sha256"],
            source_root=self.root,
            config=config,
            depth=self.config.depth,
            timeout_secs=self.config.timeout_secs,
            kill_grace_secs=self.config.kill_grace_secs,
            parent_run_id=parent_id,
            action=action_data,
            ranker=self.directory / "context/ranker-model.json"
            if self.config.ranker_model
            else None,
        )
        summary = await asyncio.to_thread(summarize_run, directory)
        p = summary["progress"]
        with self.db() as db:
            db.execute(
                """UPDATE runs SET state='finished',started_at=?,finished_at=?,termination_reason=?,
              wall_time=?,completed_depth=?,current_depth=?,current_refinement_step=?,solver_time=?,profile_path=?,summary_path=? WHERE run_id=?""",
                (
                    metadata["started_at"],
                    metadata["finished_at"],
                    metadata["termination_reason"],
                    metadata["wall_time_secs"],
                    p.get("deepest_completed_depth"),
                    p.get("current_depth"),
                    p.get("current_refinement_step"),
                    summary["solver"]["total_solver_secs"],
                    str(directory.relative_to(self.directory) / "profile.json"),
                    str(directory.relative_to(self.directory) / "summary.json"),
                    run_id,
                ),
            )
        self.event(
            benchmark_id, {"kind": "run_completed", "run_id": run_id, "outcome": summary["outcome"]}
        )
        logging.getLogger(__name__).info(
            "%s run %d/%d: %s, %.3fs",
            benchmark_id,
            ordinal,
            self.config.executions_per_benchmark,
            metadata["termination_reason"],
            metadata["wall_time_secs"],
        )
        if metadata["termination_reason"] == "spawn_error":
            raise RuntimeError(f"Could not execute Yardbird: {metadata['error']}")
        return {"run_id": run_id, "summary": summary}

    def context(self, benchmark_id: str, last_result=None) -> dict:
        pairs = self.summaries(benchmark_id)
        table = [
            {
                "run_id": row["run_id"],
                "parent_run_id": row["parent_run_id"],
                "config": json.loads(row["config_json"]),
                "hypothesis": json.loads(row["action_json"]).get("hypothesis"),
                "outcome": s["outcome"],
                "progress": s["progress"],
                "solver_secs": s["solver"].get("total_solver_secs", s["solver"]["raw_check_secs"]),
            }
            for row, s in pairs
        ]
        abstract = [
            (row, s) for row, s in pairs if json.loads(row["config_json"])["strategy"] == "abstract"
        ]
        flags = []
        if len(pairs) >= 2:
            baseline, concrete = pairs[0][1], pairs[1][1]
            ctime = concrete["outcome"].get("wall_time_secs") or 0
            btime = baseline["outcome"].get("wall_time_secs") or 0
            if concrete["outcome"]["termination_reason"] in {"proof", "depth_limit"} and (
                baseline["outcome"]["termination_reason"] not in {"proof", "depth_limit"}
                or btime > 5 * max(ctime, 0.001)
            ):
                flags.append("LARGE_CONCRETE_ABSTRACT_GAP")
        return {
            "benchmark": self.benchmarks[benchmark_id],
            "execution_budget": self.config.executions_per_benchmark,
            "runs_remaining": self.config.executions_per_benchmark - len(pairs),
            "experiments": table,
            "baseline": pairs[0][1] if pairs else None,
            "concrete": pairs[1][1] if len(pairs) > 1 else None,
            "best_abstract_run_ids": [
                row["run_id"] for row, _ in sorted(abstract, key=lambda x: ranking_key(x[1]))[:3]
            ],
            "flags": flags,
            "last_action_result": last_result,
            "ranker_model_available": self.config.ranker_model is not None,
        }
