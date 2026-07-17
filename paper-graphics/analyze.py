#!/usr/bin/env python3

from __future__ import annotations

import argparse
from pathlib import Path

from main import choose_baseline_strategy
from src.analysis import build_analysis, write_analysis_exports
from src.benchmark_parsing import BenchmarkParser


def group_results(json_files: list[Path]):
    parser = BenchmarkParser(json_files)
    grouped = {}
    strategy_keys = set()
    for result in parser.all_results:
        strategy_id = result.get_strategy_id()
        grouped.setdefault(result.example_name, {})[strategy_id] = result
        strategy_keys.add(strategy_id)
    return grouped, strategy_keys


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate reusable Yardbird benchmark analysis JSON, CSV, and Markdown"
    )
    parser.add_argument("json_files", nargs="+", type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument(
        "--baseline",
        help="Strategy id to use as the comparison baseline (default: concrete when available)",
    )
    parser.add_argument(
        "--runtime-tie-pct",
        type=float,
        default=5.0,
        help="Percent difference treated as a runtime tie (default: 5)",
    )
    args = parser.parse_args()

    grouped, strategy_keys = group_results(args.json_files)
    baseline = args.baseline or choose_baseline_strategy(strategy_keys)
    if baseline is None:
        parser.error("No strategies were found in the supplied result files")
    if baseline not in strategy_keys:
        parser.error(
            f"Unknown baseline {baseline!r}; available: {', '.join(sorted(strategy_keys))}"
        )
    if not 0 <= args.runtime_tie_pct < 100:
        parser.error("--runtime-tie-pct must be in [0, 100)")

    analysis = build_analysis(
        grouped,
        strategy_keys,
        baseline,
        runtime_tie_tolerance=args.runtime_tie_pct / 100.0,
    )
    exports = write_analysis_exports(args.output_dir, analysis)
    overview = analysis["overview"]
    print(
        f"Analyzed {overview['benchmark_count']} benchmarks across "
        f"{overview['strategy_count']} strategies using {baseline!r} as the baseline."
    )
    print(f"Analysis: {exports['analysis_json']}")
    print(f"Summary: {exports['analysis_markdown']}")
    for path in exports["data_csv"]:
        print(f"CSV: {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
