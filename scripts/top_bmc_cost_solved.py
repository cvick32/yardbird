#!/usr/bin/env python3
"""Print the longest-running benchmarks solved by abstract+bmc-cost.

This is intentionally a small throwaway helper for garden/main_eval JSON files.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


DEFAULT_SEARCH_ROOT = Path("benchmark_results/main_eval")
SOLVED_RESULT_KEYS = {"Success", "_FoundProof"}


def result_jsons(paths: list[Path]) -> list[Path]:
    files: list[Path] = []
    for path in paths:
        if path.is_file() and path.suffix == ".json":
            files.append(path)
        elif path.is_dir():
            files.extend(sorted(path.glob("raw/**/*.json")))
            files.extend(sorted(path.glob("*.json")))
        else:
            raise FileNotFoundError(path)
    return sorted(set(files))


def newest_result_json() -> Path:
    files = list(DEFAULT_SEARCH_ROOT.glob("*/raw/**/*.json"))
    if not files:
        raise FileNotFoundError(
            f"No result JSON files found under {DEFAULT_SEARCH_ROOT}"
        )
    return max(files, key=lambda path: path.stat().st_mtime)


def clean_example_name(example: str) -> str:
    if "_examples/" in example:
        return "examples/" + example.split("_examples/", 1)[1]
    return example


def is_bmc_cost_success(result: dict[str, Any]) -> bool:
    if result.get("strategy") != "abstract":
        return False
    if result.get("cost_function") not in {"bmc-cost", "symbol-cost"}:
        return False
    result_payload = result.get("result", {})
    if not isinstance(result_payload, dict):
        return False
    return any(key in result_payload for key in SOLVED_RESULT_KEYS)


def iter_bmc_cost_successes(json_path: Path):
    data = json.loads(json_path.read_text())
    for benchmark in data.get("benchmarks", []):
        example = clean_example_name(benchmark.get("example", "unknown"))
        for result in benchmark.get("result", []):
            if is_bmc_cost_success(result):
                yield {
                    "example": example,
                    "runtime_ms": int(result.get("run_time", 0)),
                    "depth": result.get("depth"),
                    "json_path": json_path,
                }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Show the longest-running benchmarks solved by abstract+bmc-cost."
    )
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help="Garden JSON files or main_eval run directories. Defaults to newest raw result JSON.",
    )
    parser.add_argument(
        "-n",
        "--limit",
        type=int,
        default=50,
        help="Number of benchmarks to print (default: 50).",
    )
    parser.add_argument(
        "--paths-only",
        action="store_true",
        help="Print only benchmark paths, one per line.",
    )
    args = parser.parse_args()

    json_files = result_jsons(args.paths) if args.paths else [newest_result_json()]
    rows = []
    for json_path in json_files:
        rows.extend(iter_bmc_cost_successes(json_path))

    rows.sort(key=lambda row: row["runtime_ms"], reverse=True)
    rows = rows[: args.limit]

    if args.paths_only:
        for row in rows:
            print(row["example"])
        return 0

    print(f"# Top {len(rows)} abstract+bmc-cost solved benchmarks")
    print("# runtime_ms\tdepth\tbenchmark")
    for row in rows:
        print(f"{row['runtime_ms']}\t{row['depth']}\t{row['example']}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
