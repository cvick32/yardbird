from __future__ import annotations

import io
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from main import generate_figures
from src.benchmark_parsing import BenchmarkResult
from src.data_generators import SolverRuntimeCactusPlotGenerator
from src.tikz_generators import CactusPlotTikzGenerator


def result(
    benchmark: str,
    solver_time_s: float,
    *,
    strategy: str = "concrete",
    cost_function: str | None = None,
    success: bool = True,
) -> BenchmarkResult:
    return BenchmarkResult(
        example_name=benchmark,
        strategy=strategy,
        cost_function=cost_function,
        runtime_ms=100,
        depth=5,
        result_type="Success" if success else "Timeout",
        success=success,
        used_instantiations=0,
        num_checks=1,
        solver_time_s=solver_time_s,
    )


class SolverRuntimeCactusTests(unittest.TestCase):
    def test_solver_times_are_sorted_by_strategy(self) -> None:
        data = SolverRuntimeCactusPlotGenerator(
            [
                result("b.vmt", 0.8),
                result("a.vmt", 0.2),
                result("c.vmt", 0.4, strategy="abstract", cost_function="bmc-cost"),
            ]
        ).generate_data()

        self.assertEqual(data["Z3 Array Theory"], [0.2, 0.8])
        self.assertEqual(data["BMC Cost"], [0.4])

    def test_failed_and_missing_solver_times_are_omitted(self) -> None:
        data = SolverRuntimeCactusPlotGenerator(
            [
                result("missing.vmt", 0.0),
                result("failed.vmt", 2.0, success=False),
                result("valid.vmt", 0.3),
            ]
        ).generate_data()

        self.assertEqual(data, {"Z3 Array Theory": [0.3]})

    def test_tikz_uses_z3_runtime_label(self) -> None:
        tikz = CactusPlotTikzGenerator.generate(
            {"Z3 Array Theory": [0.2], "BMC Cost": [0.1]},
            ylabel="Time in Z3 (s)",
            label="fig:cactus_z3_runtime",
        )

        self.assertIn(r"\label{fig:cactus_z3_runtime}", tikz)
        self.assertIn("Time in Z3 (s)", tikz)
        self.assertIn("ymin=0.08", tikz)

    def test_tikz_accepts_new_strategy_names(self) -> None:
        tikz = CactusPlotTikzGenerator.generate({"Experimental Cost": [0.2]})

        self.assertIn(r"\addplot[thick, color=black]", tikz)

    def test_figure_pipeline_writes_solver_runtime_cactus_plot(self) -> None:
        benchmark = result("examples/array/a.vmt", 0.3)
        grouped = {benchmark.example_name: {"concrete": benchmark}}

        with tempfile.TemporaryDirectory() as temp_dir:
            with redirect_stdout(io.StringIO()):
                generate_figures(
                    grouped,
                    {"concrete"},
                    [benchmark],
                    Path(temp_dir),
                )
            solver_runtime_plot = (
                Path(temp_dir) / "solver_runtime_cactus_plot.tex"
            )

            self.assertTrue(solver_runtime_plot.exists())
            self.assertIn(
                r"\label{fig:cactus_z3_runtime}",
                solver_runtime_plot.read_text(),
            )


if __name__ == "__main__":
    unittest.main()
