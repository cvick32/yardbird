from __future__ import annotations

import csv
import json
import tempfile
import unittest
from pathlib import Path

from src.analysis import build_analysis, write_analysis_exports
from src.benchmark_parsing import BenchmarkResult


def result(
    benchmark: str,
    strategy: str,
    runtime_ms: float,
    *,
    success: bool = True,
) -> BenchmarkResult:
    return BenchmarkResult(
        example_name=benchmark,
        strategy=strategy,
        cost_function="bmc-cost",
        runtime_ms=runtime_ms,
        depth=50,
        result_type="Success" if success else "Timeout",
        success=success,
        used_instantiations=10 if success else 10_000_000,
        num_checks=5 if success else 10_000_000,
        solver_time_s=runtime_ms / 2000.0 if success else 0.0,
    )


class AnalysisTests(unittest.TestCase):
    def setUp(self) -> None:
        self.grouped = {
            "examples/array/a.vmt": {
                "concrete": result("examples/array/a.vmt", "concrete", 200),
                "abstract_bmc-cost": result("examples/array/a.vmt", "abstract", 100),
            },
            "examples/array/b.vmt": {
                "concrete": result(
                    "examples/array/b.vmt", "concrete", 120_000, success=False
                ),
                "abstract_bmc-cost": result("examples/array/b.vmt", "abstract", 100),
            },
            "examples/array/c.vmt": {
                "concrete": result("examples/array/c.vmt", "concrete", 500),
                "abstract_bmc-cost": result(
                    "examples/array/c.vmt", "abstract", 120_000, success=False
                ),
            },
            "examples/array/d.vmt": {
                "concrete": result("examples/array/d.vmt", "concrete", 100),
                "abstract_bmc-cost": result("examples/array/d.vmt", "abstract", 105),
            },
            "examples/array/e.vmt": {
                "concrete": result("examples/array/e.vmt", "concrete", 500),
                "abstract_bmc-cost": result("examples/array/e.vmt", "abstract", 1_000),
            },
        }
        self.analysis = build_analysis(
            self.grouped, {"concrete", "abstract_bmc-cost"}, "concrete"
        )

    def test_solved_counts_and_comparison_categories(self) -> None:
        summaries = {
            summary["strategy_id"]: summary
            for summary in self.analysis["strategy_summaries"]
        }
        self.assertEqual(summaries["concrete"]["solved"], 4)
        self.assertEqual(summaries["abstract_bmc-cost"]["solved"], 4)
        self.assertEqual(summaries["concrete"]["exclusive_solve_count"], 1)
        self.assertEqual(summaries["abstract_bmc-cost"]["exclusive_solve_count"], 1)

        comparison = self.analysis["baseline_comparisons"][0]
        self.assertEqual(comparison["candidate_only_solved_count"], 1)
        self.assertEqual(comparison["baseline_only_solved_count"], 1)
        self.assertEqual(comparison["both_solved_count"], 3)
        self.assertEqual(comparison["runtime_win_count"], 1)
        self.assertEqual(comparison["runtime_tie_count"], 1)
        self.assertEqual(comparison["runtime_loss_count"], 1)
        self.assertEqual(
            comparison["top_runtime_wins"][0]["benchmark"], "examples/array/a.vmt"
        )
        self.assertEqual(
            comparison["top_runtime_losses"][0]["benchmark"], "examples/array/e.vmt"
        )

    def test_missing_results_are_not_counted_as_failures(self) -> None:
        del self.grouped["examples/array/e.vmt"]["abstract_bmc-cost"]
        analysis = build_analysis(
            self.grouped, {"concrete", "abstract_bmc-cost"}, "concrete"
        )
        candidate = next(
            summary
            for summary in analysis["strategy_summaries"]
            if summary["strategy_id"] == "abstract_bmc-cost"
        )
        self.assertEqual(candidate["missing_results"], 1)
        self.assertEqual(candidate["unsolved"], 1)
        self.assertEqual(analysis["baseline_comparisons"][0]["missing_result_count"], 1)

    def test_exports_are_machine_readable(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            metadata = write_analysis_exports(Path(temp_dir), self.analysis)
            analysis_json = Path(metadata["analysis_json"])
            self.assertEqual(
                json.loads(analysis_json.read_text())["schema_version"],
                "yardbird-analysis-v1",
            )
            benchmark_csv = Path(temp_dir) / "data" / "benchmark_results.csv"
            with benchmark_csv.open(newline="") as input_file:
                rows = list(csv.DictReader(input_file))
            self.assertEqual(len(rows), 10)


if __name__ == "__main__":
    unittest.main()
