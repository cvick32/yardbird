from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from main import choose_baseline_strategy
from src.benchmark_parsing import BenchmarkParser, group_benchmark_results


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
                                            "total.conflicts": 14,
                                            "decisions": 23,
                                            "abstract.decisions": 23,
                                            "total.decisions": 27,
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
        self.assertEqual(parsed.total_conflicts, 14)
        self.assertEqual(parsed.solver_time_s, 0.2)
        self.assertEqual(parsed.solver_stats["decisions"], 27)
        self.assertEqual(parsed.solver_stats["abstract.decisions"], 23)
        self.assertEqual(parsed.get_strategy_id(), "abstract_bmc-cost_cone-then-full")
        self.assertEqual(parsed.get_display_name(), "BMC Cost + Cone Then Full")

    def test_extended_ablation_policy_has_unique_identity_and_label(self) -> None:
        def entry(property_mode: str, ranker: str = "prefer-source") -> dict:
            return {
                "strategy": "abstract",
                "solver": "z3",
                "cost_function": "bmc-cost",
                "egraph_builder": "full",
                "instantiation_ranker": ranker,
                "candidate_winners_per_group": 4,
                "property_check_mode": property_mode,
                "instantiation_strategy": "full-unroll",
                "preprocess_exact_read_after_write": False,
                "run_time": 100,
                "depth": 50,
                "result": {
                    "Success": {
                        "total_instantiations_added": 2,
                        "solver_statistics": {
                            "stats": {"num checks": 3, "solver_time": 0.1}
                        },
                    }
                },
            }

        payload = {
            "metadata": {"total_benchmarks": 2},
            "benchmarks": [
                {"example": "examples/array/a.vmt", "result": [entry("scoped")]},
                {
                    "example": "examples/array/a.vmt",
                    "result": [entry("assumptions")],
                },
            ],
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "result.json"
            path.write_text(json.dumps(payload))
            results = BenchmarkParser([path]).all_results

        grouped, strategy_ids = group_benchmark_results(results)
        self.assertEqual(len(grouped), 1)
        self.assertEqual(len(strategy_ids), 2)
        self.assertNotEqual(results[0].get_strategy_id(), results[1].get_strategy_id())
        self.assertIn("N=4", results[0].get_display_name())
        self.assertIn("assuming", results[1].get_display_name())
        self.assertNotEqual(results[0].get_plot_style(), results[1].get_plot_style())

    def test_preexisting_term_cost_policy_is_the_ablation_baseline(self) -> None:
        result = BenchmarkParser.__new__(BenchmarkParser)._parse_single_result(
            "examples/array/a.vmt",
            {
                "strategy": "abstract",
                "solver": "z3",
                "cost_function": "bmc-cost",
                "egraph_builder": "full",
                "instantiation_ranker": "term-cost",
                "candidate_winners_per_group": 1,
                "property_check_mode": "scoped",
                "instantiation_strategy": "full-unroll",
                "preprocess_exact_read_after_write": False,
                "depth": 50,
                "result": {"Timeout": {}},
            },
        )
        baseline_id = result.get_strategy_id()
        self.assertEqual(choose_baseline_strategy({baseline_id, "other"}), baseline_id)


if __name__ == "__main__":
    unittest.main()
