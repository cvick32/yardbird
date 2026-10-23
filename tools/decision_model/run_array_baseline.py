#!/usr/bin/env python3
"""Sequential local array benchmark baseline. No retries; resumable, stdlib only."""
from __future__ import annotations

import argparse
from collections import Counter
import csv
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

from summarize import summarize as summarize_jev

ROOT = Path(__file__).resolve().parents[2]


def digest(path):
    checksum = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            checksum.update(chunk)
    return checksum.hexdigest()


def save_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")
    temporary.replace(path)


def read_json(path):
    try:
        value = json.loads(path.read_text())
        return value if isinstance(value, dict) else None
    except (OSError, ValueError):
        return None


def command_for(args, benchmark, case):
    command = [str(args.binary), "-f", str(benchmark), "-d", str(args.depth),
               "--wall-timeout-secs", str(args.timeout_secs), "--progress-file", str(case / "progress.json"),
               "--json-output", "--profile"]
    if args.baseline == "jev":
        command += ["--policy", "conditional-binding", "--jev-prompt", "property-directed", "--jev-batch",
                    "--jev-candidates", "10", "--jev-beam-width", "3", "--jev-attempts", "5",
                    "--jev-timeout-secs", "2", "--jev-log", str(case / "jev.jsonl")]
    else:
        command += ["--strategy", "abstract", "--cost-function", "bmc-cost", "--solver", "z3"]
    return command


def classify(result, checkpoint, returncode, forced, depth):
    progress = (result or {}).get("run_progress") or checkpoint or {}
    reason = progress.get("termination_reason")
    if forced:
        outcome = forced
    elif returncode is not None and returncode < 0:
        outcome = "process_signal"
    elif reason and reason not in ("running", "depth_limit", "proof"):
        outcome = reason
    elif returncode != 0:
        outcome = "process_error"
    elif not result:
        outcome = "invalid_json"
    elif result.get("counterexample"):
        outcome = "counterexample"
    elif result.get("found_proof") or reason == "proof":
        outcome = "proof"
    elif reason == "depth_limit" and progress.get("deepest_completed_depth") is not None and progress["deepest_completed_depth"] >= depth - 1:
        outcome = "bounded_complete"
    else:
        outcome = "incomplete"
    return outcome, progress


def stop_process(process):
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()


def run_case(args, benchmark, case):
    case.mkdir(parents=True, exist_ok=False)
    command = command_for(args, benchmark, case)
    save_json(case / "command.json", command)
    started = time.monotonic()
    forced = None
    returncode = None
    launch_error = None
    with (case / "result.json").open("w") as stdout, (case / "stderr.log").open("w") as stderr:
        try:
            process = subprocess.Popen(command, cwd=ROOT, stdout=stdout, stderr=stderr, start_new_session=True)
            try:
                returncode = process.wait(timeout=args.timeout_secs + args.grace_secs)
            except subprocess.TimeoutExpired:
                forced = "hard_timeout"
                stop_process(process)
                returncode = process.returncode
            except KeyboardInterrupt:
                forced = "interrupted"
                stop_process(process)
                returncode = process.returncode
        except OSError as error:
            forced, launch_error = "launch_error", str(error)
    elapsed = time.monotonic() - started
    result = read_json(case / "result.json")
    outcome, progress = classify(result, read_json(case / "progress.json"), returncode, forced, args.depth)
    result = result or {}
    stderr_tail = (case / "stderr.log").read_text(errors="replace")[-4000:]
    row = {"benchmark": str(benchmark.relative_to(args.examples)), "outcome": outcome,
           "returncode": returncode, "elapsed_secs": elapsed, "deepest_completed_depth": progress.get("deepest_completed_depth"),
           "current_depth": progress.get("current_depth"), "current_refinement_step": progress.get("current_refinement_step"),
           "last_completed_action": progress.get("last_completed_action"),
           "error": launch_error or progress.get("error") or (stderr_tail if outcome not in ("bounded_complete", "proof") else None),
           "installed_schemas": len(result["used_instances"]) if isinstance(result.get("used_instances"), list) else None,
           "indexed_assertions": result.get("total_instantiations_added"), "refinement_steps": result.get("total_refinement_steps"),
           "artifacts": str(case)}
    if args.baseline == "jev":
        trace = case / "jev.jsonl"
        if trace.exists():
            try:
                jev = summarize_jev(trace)
                save_json(case / "jev-summary.json", jev)
                row.update(jev_requests=jev["request_count_including_unsent"], jev_episode_outcomes=jev["episode_outcomes"],
                           jev_candidate_outcomes=jev["candidate_outcomes"], jev_known_cost_usd=jev["known_estimated_cost_usd"],
                           jev_unknown_cost_queries=jev["queries_with_unknown_cost"], jev_inference_secs=jev["inference_elapsed_secs"],
                           jev_max_request_bytes=jev["max_request_bytes"])
                errors, fallback = [], 0
                with trace.open() as stream:
                    for line in stream:
                        try:
                            event = json.loads(line)
                        except ValueError:
                            continue
                        if event.get("event") == "episode_end" and event.get("ordinary_fallback"):
                            fallback += 1
                        if event.get("event") == "transport_error" and len(errors) < 5:
                            errors.append({k: v for k, v in event.items() if k in ("error", "message", "stage", "query_id")})
                row.update(jev_fallback_requested_episodes=fallback, jev_transport_errors=errors)
            except (OSError, ValueError, KeyError, TypeError) as error:
                row["jev_summary_error"] = str(error)
        else:
            row["jev_summary_error"] = "No Jev log was produced; see process output"
    save_json(case / "summary.json", row)
    return row


def report(output, rows, total):
    outcomes = Counter(r["outcome"] for r in rows)
    episodes, candidates = Counter(), Counter()
    for row in rows:
        episodes.update(row.get("jev_episode_outcomes", {}))
        candidates.update(row.get("jev_candidate_outcomes", {}))
    summary = {"total_benchmarks": total, "finished": len(rows), "remaining": total - len(rows),
               "outcomes": dict(outcomes), "elapsed_benchmark_secs": sum(r.get("elapsed_secs", 0) for r in rows),
               "jev_episode_outcomes": dict(episodes), "jev_candidate_outcomes": dict(candidates),
               "jev_known_cost_usd": sum(r.get("jev_known_cost_usd", 0) for r in rows),
               "jev_unknown_cost_queries": sum(r.get("jev_unknown_cost_queries", 0) for r in rows),
               "benchmarks_with_jev_fallback_requested": sum(r.get("jev_fallback_requested_episodes", 0) > 0 for r in rows),
               "failure_modes": [{k: r.get(k) for k in ("benchmark", "outcome", "current_depth", "deepest_completed_depth", "error", "artifacts")}
                                 for r in rows if r["outcome"] not in ("bounded_complete", "proof")]}
    save_json(output / "summary.json", summary)
    save_json(output / "results.json", rows)
    fields = ["benchmark", "outcome", "elapsed_secs", "deepest_completed_depth", "current_depth", "current_refinement_step",
              "installed_schemas", "indexed_assertions", "jev_requests", "jev_fallback_requested_episodes",
              "jev_known_cost_usd", "jev_unknown_cost_queries", "error", "artifacts"]
    with (output / "results.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    return summary


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", choices=["jev", "yardbird"], default="jev")
    parser.add_argument("--binary", type=Path, default=ROOT / "target/quick/yardbird")
    parser.add_argument("--examples", type=Path, default=ROOT / "examples/array")
    parser.add_argument("--depth", type=int, default=20, help="Yardbird -d value: 20 checks frames 0 through 19")
    parser.add_argument("--timeout-secs", type=int, default=120, help="Cooperative wall budget per benchmark")
    parser.add_argument("--grace-secs", type=int, default=10, help="Additional seconds before process-group termination")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--resume", action="store_true", help="Skip saved summaries; do not retry partial or failed cases")
    parser.add_argument("--limit", type=int, help="Optional first N sorted benchmarks; default is all")
    parser.add_argument("--dry-run", action="store_true", help="Print commands without creating files or running Yardbird")
    args = parser.parse_args(argv)
    if not 1 <= args.depth <= 65535 or args.timeout_secs < 1 or args.grace_secs < 0 or (args.limit is not None and args.limit < 1):
        parser.error("Depth, timeout, and limit must be positive; depth <=65535 and grace >=0")
    if args.resume and (args.output is None or args.dry_run):
        parser.error("--resume requires an existing --output and cannot be combined with --dry-run")
    args.binary, args.examples = args.binary.resolve(), args.examples.resolve()
    if not args.binary.is_file() or not os.access(args.binary, os.X_OK):
        parser.error(f"Executable missing: {args.binary}. Build with cargo build --profile quick --bin yardbird")
    benchmarks = sorted(args.examples.rglob("*.vmt"))[:args.limit]
    if not benchmarks:
        parser.error(f"No .vmt benchmarks in {args.examples}")
    output = (args.output or ROOT / "benchmark_results/local_eval" / f"array-{args.baseline}-depth{args.depth}-{datetime.now(timezone.utc):%Y%m%dT%H%M%S%fZ}").resolve()
    cases = [output / "cases" / f"{i:03d}-{p.stem}" for i, p in enumerate(benchmarks, 1)]
    if args.dry_run:
        print(json.dumps({"benchmarks": len(benchmarks), "output": str(output),
                          "commands": [command_for(args, p, case) for p, case in zip(benchmarks, cases)]}, indent=2))
        return 0
    spec = {"schema_version": 1, "baseline": args.baseline, "binary": str(args.binary), "binary_sha256": digest(args.binary),
            "runner_sha256": digest(Path(__file__)), "examples": str(args.examples), "depth": args.depth,
            "timeout_secs": args.timeout_secs, "grace_secs": args.grace_secs,
            "benchmarks": [{"path": str(p.relative_to(args.examples)), "sha256": digest(p)} for p in benchmarks],
            "commands": [command_for(args, p, case) for p, case in zip(benchmarks, cases)]}
    if args.resume:
        prior = read_json(output / "manifest.json")
        if not prior or prior.get("spec") != spec:
            parser.error("Resume manifest differs from current binary, script, inputs, or settings; use a new output directory")
    else:
        if output.exists():
            parser.error("Output directory exists; use --resume or choose a new directory")
        output.mkdir(parents=True)
        git = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True)
        save_json(output / "manifest.json", {"created_at": datetime.now(timezone.utc).isoformat(), "git_commit": git.stdout.strip(), "spec": spec})
    rows = []
    print(f"{len(benchmarks)} benchmarks; {args.baseline}; -d {args.depth}; {args.timeout_secs}s + {args.grace_secs}s grace per file\nOutput: {output}", flush=True)
    for benchmark, case in zip(benchmarks, cases):
        ran_case = False
        row = read_json(case / "summary.json")
        if row is None and case.exists():
            # Do not silently repeat potentially billable calls after a runner crash.
            row = {"benchmark": str(benchmark.relative_to(args.examples)), "outcome": "interrupted_unrecorded",
                   "error": "Partial case directory retained; not retried automatically", "artifacts": str(case)}
            save_json(case / "summary.json", row)
        if row is None:
            row = run_case(args, benchmark, case)
            ran_case = True
        rows.append(row)
        report(output, rows, len(benchmarks))
        print(f"[{len(rows)}/{len(benchmarks)}] {row['benchmark']}: {row['outcome']} depth={row.get('deepest_completed_depth')} elapsed={row.get('elapsed_secs', 0):.2f}s", flush=True)
        if ran_case and row["outcome"] in ("interrupted", "launch_error"):
            return 130 if row["outcome"] == "interrupted" else 1
    print(json.dumps(report(output, rows, len(benchmarks)), indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("Interrupted; existing case artifacts are preserved. Resume with the same --output.", file=sys.stderr)
        raise SystemExit(130)
