from __future__ import annotations

import unittest

from src.benchmark_parsing import BenchmarkResult
from src.data_generators import (
    ABSTRACT_BETTER_COLOR,
    EQUAL_COLOR,
    SolverStatRatioPlotGenerator,
)


def result(strategy: str, runtime_ms: float, decisions: float) -> BenchmarkResult:
    return BenchmarkResult(
        example_name="examples/array/a.vmt",
        strategy=strategy,
        cost_function="bmc-cost" if strategy == "abstract" else None,
        runtime_ms=runtime_ms,
        depth=50,
        result_type="Success",
        success=True,
        used_instantiations=1,
        num_checks=1,
        solver_stats={"decisions": decisions},
    )


class SolverStatScatterTests(unittest.TestCase):
    def test_axes_are_counter_reduction_then_z3_speedup_and_color_uses_wall_runtime(
        self,
    ) -> None:
        grouped = {
            "examples/array/a.vmt": {
                "concrete": result("concrete", 200, 10),
                "abstract_bmc-cost": result("abstract", 100, 20),
            }
        }
        grouped["examples/array/a.vmt"]["concrete"].solver_time_s = 0.8
        grouped["examples/array/a.vmt"]["abstract_bmc-cost"].solver_time_s = 0.2
        points = SolverStatRatioPlotGenerator(grouped).generate_points(
            "concrete", "abstract_bmc-cost", "decisions"
        )

        self.assertEqual([(point.x, point.y) for point in points], [(11 / 21, 4)])
        self.assertEqual(points[0].color, ABSTRACT_BETTER_COLOR)

    def test_five_percent_runtime_band_is_a_tie(self) -> None:
        grouped = {
            "examples/array/a.vmt": {
                "concrete": result("concrete", 100, 10),
                "abstract_bmc-cost": result("abstract", 104, 20),
            }
        }
        grouped["examples/array/a.vmt"]["concrete"].solver_time_s = 0.1
        grouped["examples/array/a.vmt"]["abstract_bmc-cost"].solver_time_s = 0.1
        point = SolverStatRatioPlotGenerator(grouped).generate_points(
            "concrete", "abstract_bmc-cost", "decisions"
        )[0]

        self.assertEqual(point.color, EQUAL_COLOR)

    def test_zero_counters_use_log_safe_plus_one_ratio(self) -> None:
        grouped = {
            "examples/array/a.vmt": {
                "concrete": result("concrete", 100, 0),
                "abstract_bmc-cost": result("abstract", 100, 20),
            }
        }

        grouped["examples/array/a.vmt"]["concrete"].solver_time_s = 0.1
        grouped["examples/array/a.vmt"]["abstract_bmc-cost"].solver_time_s = 0.1
        point = SolverStatRatioPlotGenerator(grouped).generate_points(
            "concrete", "abstract_bmc-cost", "decisions"
        )
        self.assertEqual((point[0].x, point[0].y), (1 / 21, 1))


if __name__ == "__main__":
    unittest.main()
