from __future__ import annotations

import csv
import json
import math
import statistics
from collections import Counter
from pathlib import Path
from typing import Any

from .benchmark_parsing import BenchmarkResult


ANALYSIS_SCHEMA_VERSION = "yardbird-analysis-v1"
DEFAULT_RUNTIME_TIE_TOLERANCE = 0.05


def _strategy_sort_key(strategy_id: str, baseline_strategy: str) -> tuple[int, str]:
    if strategy_id == baseline_strategy:
        return (0, strategy_id)
    if strategy_id == "abstract_bmc-cost":
        return (1, strategy_id)
    if strategy_id == "abstract-with-quantifiers":
        return (2, strategy_id)
    return (3, strategy_id)


def _display_name(
    grouped_results: dict[str, dict[str, BenchmarkResult]], strategy_id: str
) -> str:
    for strategies in grouped_results.values():
        result = strategies.get(strategy_id)
        if result is not None:
            return result.get_display_name()
    return strategy_id


def _round(value: float | None, digits: int = 3) -> float | None:
    return round(value, digits) if value is not None else None


def _mean(values: list[float]) -> float | None:
    return statistics.fmean(values) if values else None


def _median(values: list[float]) -> float | None:
    return statistics.median(values) if values else None


def _geometric_mean(values: list[float]) -> float | None:
    positive = [value for value in values if value > 0]
    if not positive:
        return None
    return math.exp(sum(math.log(value) for value in positive) / len(positive))


def _benchmark_row(result: BenchmarkResult, strategy_id: str) -> dict[str, Any]:
    return {
        "benchmark": result.example_name,
        "strategy_id": strategy_id,
        "strategy": result.strategy,
        "strategy_display_name": result.get_display_name(),
        "cost_function": result.cost_function,
        "depth": result.depth,
        "result_type": result.result_type,
        "success": result.success,
        "runtime_ms": result.runtime_ms,
        "runtime_s": _round(result.runtime_ms / 1000.0),
        "solver_time_s": _round(result.solver_time_s),
        "used_instantiations": (result.used_instantiations if result.success else None),
        "num_checks": result.num_checks if result.success else None,
    }


def _comparison_row(
    benchmark: str,
    candidate_id: str,
    candidate: BenchmarkResult | None,
    baseline_id: str,
    baseline: BenchmarkResult | None,
    runtime_tie_tolerance: float,
) -> dict[str, Any]:
    category = "missing_result"
    speedup = None

    if candidate is not None and baseline is not None:
        if candidate.success and not baseline.success:
            category = "coverage_win"
        elif baseline.success and not candidate.success:
            category = "coverage_loss"
        elif not candidate.success and not baseline.success:
            category = "neither_solved"
        else:
            category = "runtime_tie"
            if candidate.runtime_ms > 0 and baseline.runtime_ms > 0:
                speedup = baseline.runtime_ms / candidate.runtime_ms
                if speedup > 1.0 + runtime_tie_tolerance:
                    category = "runtime_win"
                elif speedup < 1.0 / (1.0 + runtime_tie_tolerance):
                    category = "runtime_loss"

    return {
        "benchmark": benchmark,
        "candidate_strategy_id": candidate_id,
        "baseline_strategy_id": baseline_id,
        "category": category,
        "candidate_result_type": candidate.result_type if candidate else None,
        "baseline_result_type": baseline.result_type if baseline else None,
        "candidate_success": candidate.success if candidate else None,
        "baseline_success": baseline.success if baseline else None,
        "candidate_runtime_ms": candidate.runtime_ms if candidate else None,
        "baseline_runtime_ms": baseline.runtime_ms if baseline else None,
        "runtime_speedup": _round(speedup),
        "candidate_instantiations": (
            candidate.used_instantiations if candidate and candidate.success else None
        ),
        "baseline_instantiations": (
            baseline.used_instantiations if baseline and baseline.success else None
        ),
    }


def build_analysis(
    grouped_results: dict[str, dict[str, BenchmarkResult]],
    strategy_keys: set[str],
    baseline_strategy: str,
    runtime_tie_tolerance: float = DEFAULT_RUNTIME_TIE_TOLERANCE,
) -> dict[str, Any]:
    """Build a reusable run analysis from normalized Garden benchmark results.

    Runtime comparisons use baseline/candidate as the speedup ratio. A ratio above
    ``1 + runtime_tie_tolerance`` is a candidate win, a ratio below its reciprocal
    is a loss, and values in between are ties.
    """
    if not 0 <= runtime_tie_tolerance < 1:
        raise ValueError("runtime_tie_tolerance must be in [0, 1)")
    if strategy_keys and baseline_strategy not in strategy_keys:
        raise ValueError(f"Unknown baseline strategy: {baseline_strategy}")

    benchmarks = sorted(grouped_results)
    strategies = sorted(
        strategy_keys,
        key=lambda strategy_id: _strategy_sort_key(strategy_id, baseline_strategy),
    )
    display_names = {
        strategy_id: _display_name(grouped_results, strategy_id)
        for strategy_id in strategies
    }

    normalized_rows: list[dict[str, Any]] = []
    strategy_summaries: list[dict[str, Any]] = []
    fastest_counts = Counter()

    for benchmark, results in grouped_results.items():
        solved = [
            (strategy_id, result)
            for strategy_id, result in results.items()
            if strategy_id in strategy_keys and result.success
        ]
        if solved:
            fastest_runtime = min(result.runtime_ms for _, result in solved)
            for strategy_id, result in solved:
                if result.runtime_ms == fastest_runtime:
                    fastest_counts[strategy_id] += 1

    for strategy_id in strategies:
        results = [
            grouped_results[benchmark][strategy_id]
            for benchmark in benchmarks
            if strategy_id in grouped_results[benchmark]
        ]
        normalized_rows.extend(
            _benchmark_row(result, strategy_id) for result in results
        )
        successes = [result for result in results if result.success]
        runtimes = [result.runtime_ms / 1000.0 for result in successes]
        observed_runtimes = [result.runtime_ms / 1000.0 for result in results]
        instantiations = [
            float(result.used_instantiations)
            for result in successes
            if result.used_instantiations is not None
        ]
        solved_examples = {result.example_name for result in successes}
        exclusive_solves = [
            benchmark
            for benchmark in sorted(solved_examples)
            if not any(
                other_id != strategy_id and other_result.success
                for other_id, other_result in grouped_results[benchmark].items()
                if other_id in strategy_keys
            )
        ]
        result_types = Counter(result.result_type for result in results)

        strategy_summaries.append(
            {
                "strategy_id": strategy_id,
                "display_name": display_names[strategy_id],
                "expected_benchmarks": len(benchmarks),
                "result_count": len(results),
                "missing_results": len(benchmarks) - len(results),
                "solved": len(successes),
                "unsolved": len(results) - len(successes),
                "solve_rate_pct": _round(
                    (100.0 * len(successes) / len(results)) if results else None,
                    1,
                ),
                "coverage_of_suite_pct": _round(
                    (100.0 * len(successes) / len(benchmarks)) if benchmarks else None,
                    1,
                ),
                "result_type_counts": dict(sorted(result_types.items())),
                "total_observed_runtime_s": _round(sum(observed_runtimes)),
                "total_solved_runtime_s": _round(sum(runtimes)),
                "median_solved_runtime_s": _round(_median(runtimes)),
                "geomean_solved_runtime_s": _round(_geometric_mean(runtimes)),
                "mean_solved_runtime_s": _round(_mean(runtimes)),
                "median_instantiations": _round(_median(instantiations), 1),
                "mean_instantiations": _round(_mean(instantiations), 1),
                "fastest_solve_count": fastest_counts[strategy_id],
                "exclusive_solve_count": len(exclusive_solves),
                "exclusive_solves": exclusive_solves,
            }
        )

    comparison_rows: list[dict[str, Any]] = []
    comparison_summaries: list[dict[str, Any]] = []

    for candidate_id in strategies:
        if candidate_id == baseline_strategy:
            continue
        rows = [
            _comparison_row(
                benchmark,
                candidate_id,
                grouped_results[benchmark].get(candidate_id),
                baseline_strategy,
                grouped_results[benchmark].get(baseline_strategy),
                runtime_tie_tolerance,
            )
            for benchmark in benchmarks
        ]
        comparison_rows.extend(rows)
        counts = Counter(row["category"] for row in rows)
        shared_speedups = [
            row["runtime_speedup"] for row in rows if row["runtime_speedup"] is not None
        ]
        coverage_wins = sorted(
            (row for row in rows if row["category"] == "coverage_win"),
            key=lambda row: row["benchmark"],
        )
        coverage_losses = sorted(
            (row for row in rows if row["category"] == "coverage_loss"),
            key=lambda row: row["benchmark"],
        )
        runtime_wins = sorted(
            (row for row in rows if row["category"] == "runtime_win"),
            key=lambda row: row["runtime_speedup"],
            reverse=True,
        )
        runtime_losses = sorted(
            (row for row in rows if row["category"] == "runtime_loss"),
            key=lambda row: row["runtime_speedup"],
        )
        candidate_solved = sum(
            1
            for benchmark in benchmarks
            if (result := grouped_results[benchmark].get(candidate_id)) is not None
            and result.success
        )
        baseline_solved = sum(
            1
            for benchmark in benchmarks
            if (result := grouped_results[benchmark].get(baseline_strategy)) is not None
            and result.success
        )

        comparison_summaries.append(
            {
                "candidate_strategy_id": candidate_id,
                "candidate_display_name": display_names[candidate_id],
                "baseline_strategy_id": baseline_strategy,
                "baseline_display_name": display_names[baseline_strategy],
                "candidate_solved": candidate_solved,
                "baseline_solved": baseline_solved,
                "solve_coverage_delta": candidate_solved - baseline_solved,
                "benchmarks_with_both_results": len(benchmarks)
                - counts["missing_result"],
                "missing_result_count": counts["missing_result"],
                "candidate_only_solved_count": counts["coverage_win"],
                "baseline_only_solved_count": counts["coverage_loss"],
                "both_solved_count": counts["runtime_win"]
                + counts["runtime_tie"]
                + counts["runtime_loss"],
                "neither_solved_count": counts["neither_solved"],
                "runtime_win_count": counts["runtime_win"],
                "runtime_loss_count": counts["runtime_loss"],
                "runtime_tie_count": counts["runtime_tie"],
                "geomean_runtime_speedup": _round(_geometric_mean(shared_speedups)),
                "median_runtime_speedup": _round(_median(shared_speedups)),
                "candidate_only_solves": coverage_wins,
                "baseline_only_solves": coverage_losses,
                "top_runtime_wins": runtime_wins[:10],
                "top_runtime_losses": runtime_losses[:10],
            }
        )

    portfolio_solved = sum(
        1
        for results in grouped_results.values()
        if any(
            result.success
            for strategy_id, result in results.items()
            if strategy_id in strategy_keys
        )
    )
    complete_benchmarks = sum(
        1
        for results in grouped_results.values()
        if all(strategy_id in results for strategy_id in strategy_keys)
    )

    return {
        "schema_version": ANALYSIS_SCHEMA_VERSION,
        "baseline_strategy": baseline_strategy,
        "baseline_display_name": display_names.get(
            baseline_strategy, baseline_strategy
        ),
        "runtime_tie_tolerance_pct": runtime_tie_tolerance * 100.0,
        "overview": {
            "benchmark_count": len(benchmarks),
            "strategy_count": len(strategies),
            "result_count": len(normalized_rows),
            "expected_result_count": len(benchmarks) * len(strategies),
            "complete_benchmark_count": complete_benchmarks,
            "portfolio_solved_count": portfolio_solved,
            "portfolio_unsolved_count": len(benchmarks) - portfolio_solved,
        },
        "strategy_summaries": strategy_summaries,
        "baseline_comparisons": comparison_summaries,
        "benchmark_results": sorted(
            normalized_rows,
            key=lambda row: (row["benchmark"], row["strategy_id"]),
        ),
        "benchmark_comparisons": sorted(
            comparison_rows,
            key=lambda row: (row["candidate_strategy_id"], row["benchmark"]),
        ),
    }


def _csv_value(value: Any) -> Any:
    if isinstance(value, (dict, list)):
        return json.dumps(value, sort_keys=True)
    return value


def _write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    with path.open("w", newline="") as output:
        writer = csv.DictWriter(output, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow({field: _csv_value(row.get(field)) for field in fields})


def analysis_markdown(analysis: dict[str, Any]) -> str:
    overview = analysis["overview"]
    baseline_name = analysis["baseline_display_name"]
    lines = [
        "# Yardbird benchmark analysis",
        "",
        f"Baseline: **{baseline_name}** (`{analysis['baseline_strategy']}`)",
        "",
        f"- Benchmarks: {overview['benchmark_count']}",
        f"- Strategies: {overview['strategy_count']}",
        f"- Results: {overview['result_count']} / {overview['expected_result_count']}",
        f"- Portfolio solved: {overview['portfolio_solved_count']} / {overview['benchmark_count']}",
        "",
        "## Strategy summary",
        "",
        "| Strategy | Solved | Unsolved | Missing | Solve rate | Median runtime | Fastest | Exclusive |",
        "|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for summary in analysis["strategy_summaries"]:
        median = summary["median_solved_runtime_s"]
        median_text = f"{median:.3f}s" if median is not None else "-"
        solve_rate = summary["solve_rate_pct"]
        solve_rate_text = f"{solve_rate:.1f}%" if solve_rate is not None else "-"
        lines.append(
            f"| {summary['display_name']} | {summary['solved']} | "
            f"{summary['unsolved']} | {summary['missing_results']} | "
            f"{solve_rate_text} | {median_text} | "
            f"{summary['fastest_solve_count']} | {summary['exclusive_solve_count']} |"
        )

    for comparison in analysis["baseline_comparisons"]:
        candidate_name = comparison["candidate_display_name"]
        geomean = comparison["geomean_runtime_speedup"]
        geomean_text = f"{geomean:.3f}x" if geomean is not None else "n/a"
        lines.extend(
            [
                "",
                f"## {candidate_name} vs {baseline_name}",
                "",
                f"- Solved: {comparison['candidate_solved']} vs {comparison['baseline_solved']} "
                f"(delta {comparison['solve_coverage_delta']:+d})",
                f"- Exclusive solves: {comparison['candidate_only_solved_count']} vs "
                f"{comparison['baseline_only_solved_count']}",
                f"- Shared solved: {comparison['both_solved_count']}",
                f"- Runtime wins / ties / losses: {comparison['runtime_win_count']} / "
                f"{comparison['runtime_tie_count']} / {comparison['runtime_loss_count']}",
                f"- Geometric-mean runtime speedup: {geomean_text}",
            ]
        )

        for heading, key in (
            ("Candidate-only solves", "candidate_only_solves"),
            ("Baseline-only solves", "baseline_only_solves"),
        ):
            rows = comparison[key]
            if rows:
                lines.extend(["", f"### {heading}", ""])
                lines.extend(f"- `{row['benchmark']}`" for row in rows)

        for heading, key in (
            ("Largest runtime improvements", "top_runtime_wins"),
            ("Largest runtime regressions", "top_runtime_losses"),
        ):
            rows = comparison[key]
            if rows:
                lines.extend(
                    [
                        "",
                        f"### {heading}",
                        "",
                        "| Benchmark | Candidate | Baseline | Speedup |",
                        "|---|---:|---:|---:|",
                    ]
                )
                for row in rows:
                    lines.append(
                        f"| `{row['benchmark']}` | {row['candidate_runtime_ms'] / 1000.0:.3f}s | "
                        f"{row['baseline_runtime_ms'] / 1000.0:.3f}s | "
                        f"{row['runtime_speedup']:.3f}x |"
                    )

    lines.extend(
        [
            "",
            "Runtime speedup is baseline runtime divided by candidate runtime. "
            f"Wins and losses use a {analysis['runtime_tie_tolerance_pct']:.1f}% tie band.",
            "",
        ]
    )
    return "\n".join(lines)


def write_analysis_exports(
    report_dir: Path, analysis: dict[str, Any]
) -> dict[str, Any]:
    report_dir.mkdir(parents=True, exist_ok=True)
    data_dir = report_dir / "data"
    data_dir.mkdir(parents=True, exist_ok=True)

    analysis_json = report_dir / "analysis.json"
    analysis_md = report_dir / "analysis.md"
    analysis_json.write_text(json.dumps(analysis, indent=2, sort_keys=True) + "\n")
    analysis_md.write_text(analysis_markdown(analysis))

    strategy_csv = data_dir / "strategy_summary.csv"
    comparison_summary_csv = data_dir / "baseline_comparisons.csv"
    benchmark_results_csv = data_dir / "benchmark_results.csv"
    benchmark_comparisons_csv = data_dir / "benchmark_comparisons.csv"

    _write_csv(
        strategy_csv,
        analysis["strategy_summaries"],
        [
            "strategy_id",
            "display_name",
            "expected_benchmarks",
            "result_count",
            "missing_results",
            "solved",
            "unsolved",
            "solve_rate_pct",
            "coverage_of_suite_pct",
            "result_type_counts",
            "total_observed_runtime_s",
            "total_solved_runtime_s",
            "median_solved_runtime_s",
            "geomean_solved_runtime_s",
            "mean_solved_runtime_s",
            "median_instantiations",
            "mean_instantiations",
            "fastest_solve_count",
            "exclusive_solve_count",
        ],
    )
    _write_csv(
        comparison_summary_csv,
        analysis["baseline_comparisons"],
        [
            "candidate_strategy_id",
            "candidate_display_name",
            "baseline_strategy_id",
            "baseline_display_name",
            "candidate_solved",
            "baseline_solved",
            "solve_coverage_delta",
            "benchmarks_with_both_results",
            "missing_result_count",
            "candidate_only_solved_count",
            "baseline_only_solved_count",
            "both_solved_count",
            "neither_solved_count",
            "runtime_win_count",
            "runtime_tie_count",
            "runtime_loss_count",
            "geomean_runtime_speedup",
            "median_runtime_speedup",
        ],
    )
    _write_csv(
        benchmark_results_csv,
        analysis["benchmark_results"],
        [
            "benchmark",
            "strategy_id",
            "strategy",
            "strategy_display_name",
            "cost_function",
            "depth",
            "result_type",
            "success",
            "runtime_ms",
            "runtime_s",
            "solver_time_s",
            "used_instantiations",
            "num_checks",
        ],
    )
    _write_csv(
        benchmark_comparisons_csv,
        analysis["benchmark_comparisons"],
        [
            "benchmark",
            "candidate_strategy_id",
            "baseline_strategy_id",
            "category",
            "candidate_result_type",
            "baseline_result_type",
            "candidate_success",
            "baseline_success",
            "candidate_runtime_ms",
            "baseline_runtime_ms",
            "runtime_speedup",
            "candidate_instantiations",
            "baseline_instantiations",
        ],
    )

    return {
        "analysis_json": str(analysis_json),
        "analysis_markdown": str(analysis_md),
        "data_csv": [
            str(strategy_csv),
            str(comparison_summary_csv),
            str(benchmark_results_csv),
            str(benchmark_comparisons_csv),
        ],
    }
