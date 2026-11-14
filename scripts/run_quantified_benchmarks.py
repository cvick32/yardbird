#!/usr/bin/env python3
"""Run both Yardbird strategies on generated VMTs: -d 5, 10 seconds per run."""

import argparse
from collections import Counter
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import time


REPO = Path(__file__).resolve().parents[1]
INPUTS = REPO / "examples/quantified-transition-systems/generated-vmt"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=REPO / "target/release/yardbird")
    parser.add_argument("--filter", default="", help="Only run paths containing this substring")
    parser.add_argument("--output", type=Path, help="New JSONL results file (default: timestamped benchmark_results file)")
    args = parser.parse_args()
    binary = args.binary.resolve()
    if not binary.is_file():
        parser.error(f"Missing binary: {binary}; build with cargo build --release --bin yardbird")
    paths = [p for p in (INPUTS / "vmt-inputs.txt").read_text().splitlines()
             if p and args.filter in p]
    if not paths:
        parser.error("No benchmarks match --filter")
    for path in paths:
        if not (INPUTS / path).is_file():
            parser.error(f"Missing benchmark: {INPUTS / path}")

    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output = args.output or REPO / "benchmark_results" / f"quantified-d5-10s-{stamp}.jsonl"
    output.parent.mkdir(parents=True, exist_ok=True)
    counts = Counter()
    print(f"Running {len(paths)} benchmarks × 2 strategies; results: {output}", flush=True)
    # Flush after each run so interrupted batches retain completed results.
    with output.open("x") as results:
        for path in paths:
            for strategy in ("concrete", "abstract"):
                command = [str(binary), "-f", str(INPUTS / path), "-s", strategy,
                           "-d", "5", "--wall-timeout-secs", "10", "--json-output"]
                record = {"path": path, "strategy": strategy, "depth": 5,
                          "timeout_secs": 10, "command": command}
                started = time.monotonic()
                try:
                    proc = subprocess.run(command, capture_output=True, text=True, timeout=10)
                except subprocess.TimeoutExpired:
                    record.update(status="timeout", timeout_kind="external")
                else:
                    record.update(exit_code=proc.returncode, stderr=proc.stderr)
                    try:
                        result = json.loads(proc.stdout)
                        if not isinstance(result, dict):
                            raise ValueError("Expected a JSON object")
                    except ValueError:
                        record.update(status="error", stdout=proc.stdout)
                    else:
                        status = (result.get("run_progress") or {}).get("termination_reason", "unknown")
                        if proc.returncode != 0:
                            status = "error"
                        record.update(status=status, result=result)
                        if status == "timeout":
                            record["timeout_kind"] = "cooperative"
                record["elapsed_secs"] = round(time.monotonic() - started, 3)
                results.write(json.dumps(record) + "\n")
                results.flush()
                counts[record["status"]] += 1
                print(f"[{sum(counts.values())}/{len(paths) * 2}] {strategy:8} "
                      f"{record['status']:12} {record['elapsed_secs']:6.2f}s {path}", flush=True)
    print(json.dumps(dict(counts), sort_keys=True))


if __name__ == "__main__":
    main()
