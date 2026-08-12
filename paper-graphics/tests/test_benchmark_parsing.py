from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from src.benchmark_parsing import BenchmarkParser


class BenchmarkParserTests(unittest.TestCase):
    def test_found_proof_is_a_solved_result(self) -> None:
        payload = {
            "benchmarks": [
                {
                    "example": "deep_examples/array/proof.vmt",
                    "result": [
                        {
                            "strategy": "abstract",
                            "cost_function": "bmc-cost",
                            "egraph_builder": "cone-then-full",
                            "run_time": 250,
                            "depth": 5,
                            "result": {
                                "_FoundProof": {
                                    "total_instantiations_added": 7,
                                    "solver_statistics": {
                                        "stats": {
                                            "num checks": 3,
                                            "solver_time": 0.1,
                                            "total_solver_time": 0.2,
                                            "conflicts": 11,
                                            "decisions": 23,
                                        }
                                    },
                                }
                            },
                        }
                    ],
                }
            ]
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "result.json"
            path.write_text(json.dumps(payload))
            parsed = BenchmarkParser([path]).all_results[0]

        self.assertTrue(parsed.success)
        self.assertEqual(parsed.result_type, "_FoundProof")
        self.assertEqual(parsed.used_instantiations, 7)
        self.assertEqual(parsed.num_checks, 3)
        self.assertEqual(parsed.total_conflicts, 11)
        self.assertEqual(parsed.solver_time_s, 0.2)
        self.assertEqual(parsed.solver_stats["decisions"], 23)
        self.assertEqual(
            parsed.get_strategy_id(), "abstract_bmc-cost_cone-then-full"
        )
        self.assertEqual(parsed.get_display_name(), "BMC Cost + Cone Then Full")


if __name__ == "__main__":
    unittest.main()
