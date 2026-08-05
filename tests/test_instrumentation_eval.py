from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from tools.z3_profile.comparison import AggregateComparison, ComparisonReport
from tools.z3_profile.distribution import TimingDistribution
from yardbird_eval.cli import parse_args
from yardbird_eval.instrumentation_backend import compare_garden_suite


class InstrumentationEvalTests(unittest.TestCase):
    def test_new_command_uses_garden_run_type_vocabulary(self) -> None:
        args = parse_args(
            [
                "compare_with_instrumentation",
                "--config",
                "benchmark_config.yml",
                "--run-type",
                "small-eval",
                "--run-id",
                "test-compare",
            ]
        )

        self.assertEqual(args.command, "compare_with_instrumentation")
        self.assertEqual(args.run_type, ["small-eval"])
        self.assertEqual(args.run_id, "test-compare")
        self.assertEqual(args.warmups, 3)
        self.assertEqual(args.repetitions, 15)

    def test_generate_report_subcommand_preserves_existing_report_flow(self) -> None:
        args = parse_args(["generate-report", "--run-id", "test-compare"])

        self.assertEqual(args.command, "generate-report")
        self.assertEqual(args.run_id, "test-compare")
        self.assertTrue(args.generate_report)

    def test_garden_result_becomes_a_flattened_comparison_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            capture = root / "capture"
            capture.mkdir()
            (capture / "manifest.json").write_text(
                json.dumps(
                    {"complete": True, "benchmark_id": "examples/array/array_copy.vmt"}
                )
            )
            raw_path = root / "garden.json"
            raw_path.write_text(
                json.dumps(
                    {
                        "benchmarks": [
                            {
                                "example": "small_eval_examples/array/array_copy.vmt",
                                "result": [
                                    {
                                        "solver": "z3",
                                        "strategy": "concrete",
                                        "cost_function": "bmc-cost",
                                        "depth": 5,
                                        "run_time": 12,
                                        "solver_capture_dir": str(capture),
                                        "result": {"Success": {}},
                                    }
                                ],
                            }
                        ]
                    }
                )
            )

            aggregate = AggregateComparison(
                check_count=2,
                depth_count=2,
                stock_external=TimingDistribution((10_000_000,), 10_000_000, 0),
                instrumented_external=TimingDistribution((11_000_000,), 11_000_000, 0),
                external_overhead=TimingDistribution((1_000_000,), 1_000_000, 0),
                instrumented_internal=TimingDistribution((8_000_000,), 8_000_000, 0),
                array_envelope=TimingDistribution((2_000_000,), 2_000_000, 0),
                non_array_residual=TimingDistribution((6_000_000,), 6_000_000, 0),
            )
            report = ComparisonReport(
                capture_dir=str(capture),
                stock_binary="stock-z3",
                instrumented_binary="instrumented-z3",
                warmups=0,
                repetitions=1,
                aggregate=aggregate,
                checks=(),
                depths=(),
            )

            entries = compare_garden_suite(
                raw_path,
                root / "comparisons",
                {},
                warmups=0,
                repetitions=1,
                timeout_seconds=5,
                compare=lambda *args, **kwargs: report,
            )

            self.assertEqual(len(entries), 1)
            entry = entries[0]
            self.assertEqual(entry["comparison_status"], "completed")
            self.assertEqual(entry["example"], "examples/array/array_copy.vmt")
            self.assertEqual(entry["metrics"]["external_overhead_pct"], 10.0)
            self.assertEqual(entry["metrics"]["array_fraction_pct"], 25.0)
            self.assertTrue(Path(entry["comparison_path"]).is_file())

    def test_unsolved_garden_result_is_retained_as_unavailable(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            raw_path = root / "garden.json"
            raw_path.write_text(
                json.dumps(
                    {
                        "benchmarks": [
                            {
                                "example": "examples/array/slow.vmt",
                                "result": [
                                    {
                                        "solver": "z3",
                                        "strategy": "abstract",
                                        "cost_function": "bmc-cost",
                                        "depth": 5,
                                        "run_time": 5000,
                                        "solver_capture_dir": str(root / "missing"),
                                        "result": {"Timeout": 5000},
                                    }
                                ],
                            }
                        ]
                    }
                )
            )

            entries = compare_garden_suite(
                raw_path,
                root / "comparisons",
                {},
                warmups=0,
                repetitions=1,
                timeout_seconds=5,
            )

            self.assertEqual(entries[0]["comparison_status"], "unavailable")
            self.assertIn("Timeout", entries[0]["comparison_error"])

    def test_empty_garden_matrix_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            raw_path = root / "garden.json"
            raw_path.write_text(json.dumps({"benchmarks": []}))

            with self.assertRaisesRegex(RuntimeError, "no benchmark results"):
                compare_garden_suite(
                    raw_path,
                    root / "comparisons",
                    {},
                    warmups=0,
                    repetitions=1,
                    timeout_seconds=5,
                )


if __name__ == "__main__":
    unittest.main()
