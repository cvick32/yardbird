import unittest

from src.benchmark_parsing import BenchmarkParser
from src.data_generators import CactusPlotGenerator, RuntimeScatterPlotGenerator
from src.tikz_generators import TableTikzGenerator


class RuntimeTimeoutTests(unittest.TestCase):
    def parse(self, outcome, elapsed):
        return BenchmarkParser.__new__(BenchmarkParser)._parse_single_result(
            "example",
            {"strategy": "concrete", "run_time": elapsed, "result": outcome},
        )

    def test_plots_use_each_recorded_timeout(self):
        first = self.parse({"Timeout": 500000}, 500123)
        second = self.parse({"Timeout": 30000}, 30100)
        self.assertEqual(
            CactusPlotGenerator([first, second]).generate_data(),
            {"Z3 Array Theory": [30.0, 500.0]},
        )
        point = RuntimeScatterPlotGenerator(
            {"example": {"a": first, "b": second}}
        ).generate_points("a", "b")[0]
        self.assertEqual((point.x, point.y), (500.0, 30.0))

    def test_other_results_keep_elapsed_runtime(self):
        results = [
            self.parse({"Success": {"solver_statistics": {"stats": {}}}}, 250),
            self.parse({"Error": "failed"}, 1500),
            self.parse({"Timeout": None}, 31000),
        ]
        self.assertEqual(
            CactusPlotGenerator(results).generate_data(),
            {"Z3 Array Theory": [0.25, 1.5, 31.0]},
        )

    def test_caption_uses_observed_timeout_limits(self):
        for outcomes, expected in [
            ([{"Timeout": 500000}], "timeout (500s)"),
            ([{"Timeout": 500000}, {"Timeout": 30000}], "timeout (30s, 500s)"),
            ([{"Error": "failed"}], "timeout, ERR"),
        ]:
            grouped = {
                str(i): {"concrete": self.parse(outcome, 1)}
                for i, outcome in enumerate(outcomes)
            }
            table = TableTikzGenerator.generate_all_benchmarks_table(
                grouped, {"concrete"}
            )
            self.assertIn(expected, table)
            self.assertNotIn("120s", table)
