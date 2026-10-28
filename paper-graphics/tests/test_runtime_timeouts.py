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

    def test_cactus_excludes_timeouts_but_scatter_uses_recorded_limits(self):
        first = self.parse({"Timeout": 500000}, 500123)
        second = self.parse({"Timeout": 30000}, 30100)
        self.assertEqual(
            CactusPlotGenerator([first, second]).generate_data(),
            {"Z3 Array Theory": []},
        )
        point = RuntimeScatterPlotGenerator(
            {"example": {"a": first, "b": second}}
        ).generate_points("a", "b")[0]
        self.assertEqual((point.x, point.y), (500.0, 30.0))

    def test_cactus_counts_only_solved_results(self):
        results = [
            self.parse({"Success": {"solver_statistics": {"stats": {}}}}, 250),
            self.parse({"Error": "failed"}, 1500),
            self.parse({"Timeout": None}, 31000),
            self.parse({"NoProgress": {}}, 2000),
            self.parse({"_FoundProof": {"solver_statistics": {"stats": {}}}}, 500),
        ]
        self.assertEqual(
            CactusPlotGenerator(results).generate_data(),
            {"Z3 Array Theory": [0.25, 0.5]},
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
