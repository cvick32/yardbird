#!/usr/bin/env python3
"""Compare quantified VMT policies against native Z3 at identical BMC bounds.

Runs sequentially; records commands, binary/input hashes, partial depth progress,
and optional profiling. A depth-limit result is bounded safety, not a proof.
"""

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import fcntl
import os
import json
from pathlib import Path
import subprocess
import time


REPO = Path(__file__).resolve().parents[1]
INPUTS = REPO / "notes/quantified-search/inputs.txt"
VARIANTS = {
    "z3": ["--strategy", "concrete"],
    "z3-assuming": ["--strategy", "concrete", "--property-check-mode", "assumptions"],
    "abstract": ["--strategy", "abstract"],
    "abstract-owned": ["--strategy", "abstract", "--theory", "array,quantifiers"],
    "batch20": ["--candidate-winners-per-group", "20"],
    "batch100": ["--candidate-winners-per-group", "100"],
    "german-fast": ["--policy", "german-fast", "--theory", "array,quantifiers"],
    "guided4096": ["--policy", "countermodel-guided", "--theory", "array,quantifiers",
                   "--guidance-schedule", "supplement", "--guidance-work", "4096",
                   "--guidance-transition-order", "predecessor-first",
                   "--guidance-action-requirements", "when-unproductive"],
    "eager20": ["--eager", "--candidate-winners-per-group", "20"],
    "guided": ["--policy", "countermodel-guided"],
    "supplement": ["--policy", "countermodel-guided", "--guidance-schedule", "supplement"],
    "native-arrays": ["--theory", "quantifiers", "--candidate-winners-per-group", "20"],
    "native-quantifiers": ["--theory", "array", "--candidate-winners-per-group", "20"],
}

VARIANTS["guided4096-exact"] = [*VARIANTS["guided4096"], "--guided-exact-grounding"]
VARIANTS["guided4096-captures"] = [*VARIANTS["guided4096"], "--guided-source-captures"]
VARIANTS["guided4096-frontiers"] = [*VARIANTS["guided4096-captures"], "--guided-read-frontiers"]
VARIANTS["guided4096-read-support"] = [*VARIANTS["guided4096-frontiers"], "--guided-read-support"]
VARIANTS["guided4096-proved-prefix"] = [*VARIANTS["guided4096-read-support"], "--reuse-proved-properties"]
VARIANTS["guided4096-proved-instances"] = [*VARIANTS["guided4096-proved-prefix"], "--proved-property-instance-limit", "512"]
VARIANTS["guided4096-split-properties"] = [*VARIANTS["guided4096-proved-instances"], "--split-property-checks"]



def read_json(path):
    try:
        value = json.loads(path.read_text())
        return value if isinstance(value, dict) else {}
    except (ValueError, FileNotFoundError):
        return {}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def profile_summary(profile):
    driver, cost, operations, calls, selected = (Counter() for _ in range(5))
    batches = []
    counters = Counter()
    for row in profile.get("driver_records", []):
        driver.update(row.get("timing_secs", {}))
    for row in profile.get("cost_records", []):
        cost.update(row.get("timing_secs", {}))
        counters.update(row.get("counters", {}))
        productive, rules, instances = 0, set(), 0
        for event in row.get("effort", []):
            if event.get("kind") != "operation":
                continue
            operation = event["operation"].split("(")[0]
            operations[operation] += event["elapsed_secs"]
            calls[operation] += 1
            selected[operation] += event["report"]["selected"]
            if event["report"]["selected"]:
                productive += 1
                instances += event["report"]["selected"]
                rules.update(c["rule"] for c in event.get("candidates", []) if c["selected"])
        if productive:
            batches.append(dict(productive_operations=productive, distinct_rules=len(rules),
                                selected_instances=instances))
    # Timers are nested: these maps must not be added together.
    return dict(driver_secs=driver, cost_secs=cost, counters=counters, operation_secs=operations,
                operation_calls=calls, operation_selected=selected,
                solver_checks=len(profile.get("solver_checks", [])), batches=batches)


def run(binary, path, variant, depth, timeout, grace, profile, stem):
    # Named policies choose Z3 themselves and reject an explicit --solver.
    command = [str(binary), "-f", str(path), "-d", str(depth),
               "--wall-timeout-secs", str(timeout), "--json-output",
               "--progress-file", str(stem.with_suffix(".progress.json")),
               *VARIANTS[variant]]
    if profile:
        command.append("--profile")
    started = time.monotonic()
    returncode = None
    with stem.with_suffix(".json").open("w") as stdout, stem.with_suffix(".log").open("w") as stderr:
        try:
            process = subprocess.run(command, cwd=REPO, stdout=stdout, stderr=stderr,
                                     timeout=timeout + grace)
            returncode = process.returncode
        except subprocess.TimeoutExpired:
            pass
    elapsed = time.monotonic() - started
    result = read_json(stem.with_suffix(".json"))
    progress = result.get("run_progress") or read_json(stem.with_suffix(".progress.json"))
    if returncode is None:
        status = "external_timeout"
    elif result.get("counterexample"):
        # Yardbird reports a validated counterexample with a nonzero exit code.
        status = "counterexample"
    elif returncode != 0:
        status = "error"
    else:
        status = (result.get("run_progress") or {}).get("termination_reason", "invalid_output")
        if status == "depth_limit" and (
            [row.get("depth") for row in progress.get("depth_completions", [])] != list(range(depth))
            or progress.get("deepest_completed_depth") != depth - 1
            or result.get("counterexample") is not False
        ):
            status = "invalid_completion"
    return dict(path=str(path), variant=variant, status=status, elapsed_secs=elapsed,
                returncode=returncode, command=command, artifact=stem.name,
                progress=progress, counterexample=result.get("counterexample"),
                found_proof=result.get("found_proof"),
                refinements=result.get("total_refinement_steps"),
                instances=result.get("total_instantiations_added"),
                profile=profile_summary(result.get("profiling", {})))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=REPO / "target/release/yardbird")
    parser.add_argument("--inputs", type=Path, default=INPUTS,
                        help="Newline-separated VMT paths; use a subset for exploration")
    parser.add_argument("--input-root", type=Path, default=REPO,
                        help="Base for relative paths in --inputs")
    parser.add_argument("--filter", default="")
    parser.add_argument("--variants", nargs="+", choices=VARIANTS,
                        default=["z3", "abstract", "batch20", "eager20", "supplement", "native-quantifiers"])
    parser.add_argument("--depth", type=int, default=5)
    parser.add_argument("--timeout-secs", type=int, default=10)
    parser.add_argument("--external-grace-secs", type=float, default=2)
    parser.add_argument("--repeat", type=int, default=1)
    parser.add_argument("--profile", action="store_true",
                        help="Capture diagnostic profiles; omit for confirmation timings")
    parser.add_argument("--output", type=Path, required=True, help="Output directory")
    parser.add_argument("--resume", action="store_true", help="Resume matching metadata without repeating recorded runs")
    args = parser.parse_args()
    if min(args.depth, args.timeout_secs, args.repeat) <= 0 or args.external_grace_secs < 0:
        parser.error("depth, timeout and repeat must be positive; grace must be nonnegative")
    if args.depth > 65535:
        parser.error("depth must fit Yardbird's u16 depth")
    binary = args.binary.resolve()
    if not binary.is_file():
        parser.error(f"Missing binary: {binary}")
    paths = list(dict.fromkeys((args.input_root / line.strip()).resolve()
                              for line in args.inputs.read_text().splitlines()
                              if line.strip() and not line.lstrip().startswith("#")
                              and args.filter in line))
    if not paths:
        parser.error("No inputs selected")
    for path in paths:
        if not path.is_file():
            parser.error(f"Missing input: {path}")
    output = args.output.resolve()
    if output.exists() and not args.resume:
        parser.error(f"Output directory already exists: {output}; use --resume")
    if args.resume and not (output / "metadata.json").is_file():
        parser.error("--resume requires existing metadata")
    output.mkdir(parents=True, exist_ok=args.resume)
    lock = (output / ".runner.lock").open("a+")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        parser.error("Another runner already holds this output directory")
    lock.seek(0)
    lock.truncate()
    lock.write(str(os.getpid()))
    lock.flush()
    # Include staged edits as well as working-tree edits in build provenance.
    modified = sorted(set(
        subprocess.check_output(["git", "diff", "--name-only", "HEAD"], cwd=REPO, text=True).splitlines()
        + subprocess.check_output(["git", "ls-files", "-o", "--exclude-standard"], cwd=REPO, text=True).splitlines()
    ))
    metadata = dict(started_utc=datetime.now(timezone.utc).isoformat(),
                    revision=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
                    worktree_status=subprocess.check_output(["git", "status", "--short"], cwd=REPO, text=True),
                    binary=str(binary), binary_sha256=sha256(binary),
                    inputs={str(path): sha256(path) for path in paths},
                    input_order=[str(path) for path in paths], variant_order=args.variants,
                    variants={name: VARIANTS[name] for name in args.variants},
                    depth=args.depth, timeout_secs=args.timeout_secs,
                    external_grace_secs=args.external_grace_secs,
                    repeat=args.repeat, profile=args.profile, jobs=1,
                    source_hashes={name: sha256(REPO / name) for name in modified if (REPO / name).is_file()})
    previous = []
    if args.resume:
        old = read_json(output / "metadata.json")
        for key in ["revision", "binary_sha256", "source_hashes", "inputs", "input_order", "variant_order", "variants", "depth", "timeout_secs", "external_grace_secs", "repeat", "profile", "jobs"]:
            if old.get(key) != metadata[key]:
                parser.error(f"Cannot resume: {key} differs")
        if (output / "results.jsonl").exists():
            previous = [json.loads(line) for line in (output / "results.jsonl").read_text().splitlines()]
    else:
        (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    done = set()
    expected = {(r, str(p), v) for r in range(args.repeat) for p in paths for v in args.variants}
    counts = Counter()
    for record in previous:
        key = (record["repeat"], record["path"], record["variant"])
        if key not in expected or key in done:
            parser.error("Unexpected or duplicate checkpoint record")
        done.add(key)
        counts[f"{record['variant']}:{record['status']}"] += 1
    with (output / "results.jsonl").open("a" if args.resume else "x") as results:
        for repeat in range(args.repeat):
            for index, path in enumerate(paths):
                # Alternate order across cases and repeats.
                offset = (repeat + index) % len(args.variants)
                variants = args.variants[offset:] + args.variants[:offset]
                for variant in variants:
                    if (repeat, str(path), variant) in done:
                        continue
                    if sha256(binary) != metadata["binary_sha256"] or sha256(path) != metadata["inputs"][str(path)]:
                        parser.error("Binary or input changed during the benchmark")
                    stem = output / f"r{repeat:02}-{index:03}-{variant}"
                    if args.resume:
                        leftovers = list(output.glob(stem.name + ".*"))
                        if leftovers:
                            archive = output / "interrupted" / (stem.name + "-" + str(time.time_ns()))
                            archive.mkdir(parents=True)
                            for leftover in leftovers:
                                leftover.rename(archive / leftover.name)
                    (output / "status.json").write_text(json.dumps(dict(
                        status="running", completed=len(done), total=len(expected),
                        path=str(path), variant=variant, artifact=stem.name,
                        started_utc=datetime.now(timezone.utc).isoformat()), indent=2) + "\n")
                    record = run(binary, path, variant, args.depth, args.timeout_secs,
                                 args.external_grace_secs, args.profile, stem)
                    record["repeat"] = repeat
                    results.write(json.dumps(record) + "\n")
                    results.flush()
                    os.fsync(results.fileno())
                    done.add((repeat, str(path), variant))
                    counts[f"{variant}:{record['status']}"] += 1
                    print(f"{repeat} {path.name} {variant}: {record['status']} "
                          f"{record['elapsed_secs']:.3f}s", flush=True)
    (output / "summary.json").write_text(json.dumps(counts, indent=2) + "\n")
    (output / "status.json").write_text(json.dumps(dict(status="complete", completed=len(done), total=len(expected)), indent=2) + "\n")


if __name__ == "__main__":
    main()
