#!/usr/bin/env python3
"""Run both strategies on identical *.encoding.vmt inputs, with strict outcomes."""

import argparse
import concurrent.futures
import json
import os
import subprocess
import time
from collections import Counter
from pathlib import Path


def classify(code, data, error, depth):
    if code is None:
        return "timeout"
    if ("Solver returned unknown" in error
            or any(result.get("result") == "Unknown" for result in data.get("results", []))):
        return "unknown"
    if "Found counter-example" in error or data.get("counterexample") is True:
        return "counterexample"
    if "Abstract refinement exhausted" in error:
        return "exhausted"
    if code != 0:
        return "error"
    if (data.get("counterexample") is False
            and len(data.get("unsat_events", [])) == depth):
        return "completed"
    return "incomplete"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=Path("target/release/yardbird"))
    parser.add_argument("--root", type=Path, default=Path("examples/distributed_protocols"))
    parser.add_argument("--depth", type=int, default=5)
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.depth < 1 or args.timeout <= 0 or args.jobs < 1:
        parser.error("depth, timeout, and jobs must be positive")
    files = sorted(args.root.glob("*/*.encoding.vmt"))
    if not files:
        parser.error("no encoding companions found")
    args.output.mkdir(parents=True, exist_ok=False)
    results = []

    def run(file, strategy):
        directory = args.output / strategy
        stem = file.name.removesuffix(".encoding.vmt")
        stdout = directory / f"{stem}.json"
        stderr = directory / f"{stem}.log"
        start = time.monotonic()
        with stdout.open("w") as out, stderr.open("w") as err:
            process = subprocess.Popen(
                [str(args.binary), "-f", str(file), "-s", strategy,
                 "-d", str(args.depth), "--json-output"], stdout=out, stderr=err,
                env={**os.environ, "RUST_LOG": "off"})
            try:
                code = process.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
                code = None
        try:
            data = json.loads(stdout.read_text())
        except json.JSONDecodeError:
            data = {}
        error = stderr.read_text()
        row = {"protocol": stem, "file": str(file), "strategy": strategy,
               "exit": code, "seconds": round(time.monotonic() - start, 3),
               "outcome": classify(code, data, error, args.depth),
               "checked_depths": len(data.get("unsat_events", [])),
               "instantiations": data.get("total_instantiations_added")}
        if error:
            row["error"] = error[-2000:]
        print(json.dumps(row), flush=True)
        return row

    # Strategies run separately so they do not compete with one another.
    for strategy in ("concrete", "abstract"):
        (args.output / strategy).mkdir()
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            results.extend(pool.map(lambda file: run(file, strategy), files))
        (args.output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(strategy, dict(Counter(r["outcome"] for r in results
                                     if r["strategy"] == strategy)), flush=True)
    report = ["# Lambda-free encoding comparison", "",
              f"Both strategies use the same {len(files)} companion files and binary. "
              f"`-d {args.depth}` checks depths 0–{args.depth - 1}, with a "
              f"{args.timeout:g}s process limit and {args.jobs} workers. "
              "Strategies run separately.", "",
              "Completed means every requested depth was UNSAT. Unknown, incomplete, "
              "timeout, exhaustion, and counterexample are separate outcomes.", "",
              "| Protocol | Concrete | Seconds | Abstract | Seconds | Abstract instances |",
              "|---|---|---:|---|---:|---:|"]
    for file in files:
        c, a = [next(r for r in results if r["file"] == str(file) and r["strategy"] == s)
                for s in ("concrete", "abstract")]
        report.append(f"| {c['protocol']} | {c['outcome']} | {c['seconds']} | "
                      f"{a['outcome']} | {a['seconds']} | {a['instantiations']} |")
    report += ["", "| Outcome | Concrete | Abstract |", "|---|---:|---:|"]
    for outcome in ("completed", "unknown", "timeout", "exhausted", "counterexample", "incomplete", "error"):
        counts = [sum(r["strategy"] == s and r["outcome"] == outcome for r in results)
                  for s in ("concrete", "abstract")]
        report.append(f"| {outcome} | {counts[0]} | {counts[1]} |")
    report += ["", "The encodings preserve semantics and remove lambda expressions. "
               "The strategies still differ in both array reasoning and quantifier instantiation; "
               "this is not an isolated quantifier-instantiation experiment."]
    (args.output / "README.md").write_text("\n".join(report) + "\n")


if __name__ == "__main__":
    main()
