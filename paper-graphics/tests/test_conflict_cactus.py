from __future__ import annotations

import io
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from main import generate_figures
from src.benchmark_parsing import BenchmarkResult
from src.data_generators import ConflictCactusPlotGenerator
from src.tikz_generators import ConflictCactusPlotTikzGenerator


def result(
    benchmark: str,
    conflicts: float | None,
    *,
    success: bool = True,
) -> BenchmarkResult:
    return BenchmarkResult(
        example_name=benchmark,
        strategy="concrete",
        cost_function=None,
        runtime_ms=100,
        depth=5,
        result_type="Success" if success else "Timeout",
        success=success,
        used_instantiations=0,
        num_checks=1,
        total_conflicts=conflicts,
    )


class ConflictCactusTests(unittest.TestCase):
    def test_conflicts_are_sorted_and_missing_values_are_last(self) -> None:
        data = ConflictCactusPlotGenerator(
            [
                result("b.vmt", 8),
                result("a.vmt", 0),
                result("c.vmt", None),
                result("d.vmt", 100, success=False),
            ]
        ).generate_data()

        self.assertEqual(data["Z3 Array Theory"], [0, 8, None, None])

    def test_tikz_uses_conflict_label_and_handles_zero_conflicts(self) -> None:
        tikz = ConflictCactusPlotTikzGenerator.generate(
            {"Z3 Array Theory": [0, 8, None]}
        )

        self.assertIn(r"\label{fig:cactus_conflicts}", tikz)
        self.assertIn("Total Solver Conflicts", tikz)
        self.assertIn("(1, 1)", tikz)
        self.assertNotIn("(3,", tikz)

    def test_strategies_without_conflict_statistics_are_omitted(self) -> None:
        data = ConflictCactusPlotGenerator(
            [result("a.vmt", None), result("b.vmt", None, success=False)]
        ).generate_data()

        self.assertEqual(data, {})

    def test_figure_pipeline_writes_conflict_cactus_plot(self) -> None:
        benchmark = result("examples/array/a.vmt", 8)
        grouped = {benchmark.example_name: {"concrete": benchmark}}

        with tempfile.TemporaryDirectory() as temp_dir:
            with redirect_stdout(io.StringIO()):
                generate_figures(
                    grouped,
                    {"concrete"},
                    [benchmark],
                    Path(temp_dir),
                )
            conflict_plot = Path(temp_dir) / "conflict_cactus_plot.tex"

            self.assertTrue(conflict_plot.exists())
            self.assertIn(
                r"\label{fig:cactus_conflicts}",
                conflict_plot.read_text(),
            )


if __name__ == "__main__":
    unittest.main()
