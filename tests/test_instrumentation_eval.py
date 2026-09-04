from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

from tools.z3_profile.comparison import AggregateComparison, ComparisonReport
from tools.z3_profile.distribution import TimingDistribution
from yardbird_eval.cli import parse_args
from yardbird_eval.instrumentation_backend import compare_garden_suite, prepare_z3_build


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

    def test_downloaded_instrumentation_command_reuses_z3_replay_options(self) -> None:
        args = parse_args(
            [
                "compare-downloaded-instrumentation",
                "--run-id",
                "deep-aws-run",
                "--warmups",
                "1",
                "--repetitions",
                "5",
                "--resume",
            ]
        )

        self.assertEqual(args.command, "compare_downloaded_instrumentation")
        self.assertEqual(args.run_id, "deep-aws-run")
        self.assertEqual(args.warmups, 1)
        self.assertEqual(args.repetitions, 5)
        self.assertTrue(args.resume)

    def test_downloaded_instrumentation_does_not_resume_by_default(self) -> None:
        args = parse_args(
            ["compare-downloaded-instrumentation", "--run-id", "deep-aws-run"]
        )

        self.assertFalse(args.resume)

    def test_resume_preserves_the_original_builder_manifest_snapshot(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            build_dir = root / "build"
            build_dir.mkdir()
            current = {"builds": {"stock": {}, "instrumented": {}}}
            (build_dir / "manifest.json").write_text(json.dumps(current))
            run_dir = root / "run"
            snapshot = run_dir / "instrumentation" / "z3-builder-manifest.json"
            snapshot.parent.mkdir(parents=True)
            original = {"builds": {"stock": {"binary_sha256": "original"}}}
            snapshot.write_text(json.dumps(original))
            args = SimpleNamespace(z3_build_dir=str(build_dir), resume=True)

            _, loaded = prepare_z3_build(args, run_dir)

            self.assertEqual(loaded, current)
            self.assertEqual(json.loads(snapshot.read_text()), original)

    def test_aws_solver_journaling_is_explicitly_opt_in(self) -> None:
        ordinary = parse_args(
            ["--env", "aws", "--benchmark-type", "deep-abstract"]
        )
        captured = parse_args(
            [
                "--env",
                "aws",
                "--benchmark-type",
                "deep-abstract",
                "--capture-solver-journals",
            ]
        )

        self.assertFalse(ordinary.capture_solver_journals)
        self.assertTrue(captured.capture_solver_journals)

    def test_auxiliary_synthesis_is_explicitly_opt_in(self) -> None:
        ordinary = parse_args(
            ["--env", "aws", "--benchmark-type", "array-best-depth50"]
        )
        auxiliary = parse_args(
            [
                "--env",
                "aws",
                "--benchmark-type",
                "array-best-depth50",
                "--synthesis-trigger",
                "non-local",
                "--synthesis-guard-policy",
                "interpolant",
            ]
        )

        self.assertEqual(ordinary.synthesis_trigger, "off")
        self.assertEqual(ordinary.synthesis_guard_policy, "true")
        self.assertEqual(auxiliary.synthesis_trigger, "non-local")
        self.assertEqual(auxiliary.synthesis_guard_policy, "interpolant")

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

    def test_resume_reuses_a_compatible_existing_comparison(self) -> None:
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
                                "example": "examples/array/array_copy.vmt",
                                "result": [
                                    {
                                        "solver": "z3",
                                        "strategy": "abstract",
                                        "cost_function": "bmc-cost",
                                        "depth": 50,
                                        "run_time": 25,
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
                check_count=1,
                depth_count=1,
                stock_external=TimingDistribution((10,), 10, 0),
                instrumented_external=TimingDistribution((11,), 11, 0),
                external_overhead=TimingDistribution((1,), 1, 0),
                instrumented_internal=TimingDistribution((8,), 8, 0),
                array_envelope=TimingDistribution((2,), 2, 0),
                non_array_residual=TimingDistribution((6,), 6, 0),
            )
            report = ComparisonReport(
                capture_dir=str(capture.resolve()),
                stock_binary=str((root / "stock-z3").resolve()),
                instrumented_binary=str((root / "instrumented-z3").resolve()),
                warmups=1,
                repetitions=5,
                aggregate=aggregate,
                checks=(),
                depths=(),
            )
            comparison_dir = root / "comparisons"
            comparison_dir.mkdir()
            (comparison_dir / "00000.json").write_text(json.dumps(report.to_dict()))
            builder_manifest = {
                "builds": {
                    "stock": {"binary": report.stock_binary},
                    "instrumented": {"binary": report.instrumented_binary},
                }
            }

            def should_not_compare(*args, **kwargs):
                self.fail("resume should not replay an existing comparison")

            entries = compare_garden_suite(
                raw_path,
                comparison_dir,
                builder_manifest,
                warmups=1,
                repetitions=5,
                timeout_seconds=5,
                resume=True,
                compare=should_not_compare,
            )

            self.assertEqual(entries[0]["comparison_status"], "completed")
            self.assertEqual(entries[0]["metrics"]["array_fraction_pct"], 25.0)

    def test_resume_rejects_an_existing_comparison_with_different_parameters(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            capture = root / "capture"
            capture.mkdir()
            (capture / "manifest.json").write_text(json.dumps({"complete": True}))
            raw_path = root / "garden.json"
            raw_path.write_text(
                json.dumps(
                    {
                        "benchmarks": [
                            {
                                "example": "examples/array/array_copy.vmt",
                                "result": [
                                    {
                                        "solver": "z3",
                                        "strategy": "abstract",
                                        "solver_capture_dir": str(capture),
                                        "result": {"Success": {}},
                                    }
                                ],
                            }
                        ]
                    }
                )
            )
            comparison_dir = root / "comparisons"
            comparison_dir.mkdir()
            (comparison_dir / "00000.json").write_text(
                json.dumps(
                    {
                        "capture_dir": str(capture.resolve()),
                        "stock_binary": str((root / "stock-z3").resolve()),
                        "instrumented_binary": str(
                            (root / "instrumented-z3").resolve()
                        ),
                        "warmups": 3,
                        "repetitions": 5,
                        "aggregate": {},
                        "checks": [],
                        "depths": [],
                    }
                )
            )
            builder_manifest = {
                "builds": {
                    "stock": {"binary": str((root / "stock-z3").resolve())},
                    "instrumented": {
                        "binary": str((root / "instrumented-z3").resolve())
                    },
                }
            }

            with self.assertRaisesRegex(RuntimeError, "warmups"):
                compare_garden_suite(
                    raw_path,
                    comparison_dir,
                    builder_manifest,
                    warmups=1,
                    repetitions=5,
                    timeout_seconds=5,
                    resume=True,
                )

    def test_downloaded_worker_capture_path_is_rebased_to_local_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            capture_root = root / "captures"
            capture = capture_root / "0000" / "0007"
            capture.mkdir(parents=True)
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
                                "example": "deep_examples/array/array_copy.vmt",
                                "result": [
                                    {
                                        "solver": "z3",
                                        "strategy": "abstract",
                                        "cost_function": "bmc-cost",
                                        "depth": 50,
                                        "run_time": 25,
                                        "solver_capture_dir": (
                                            "/home/ubuntu/yardbird/worker-captures/0000/0007"
                                        ),
                                        "result": {"Success": {}},
                                    }
                                ],
                            }
                        ]
                    }
                )
            )

            aggregate = AggregateComparison(
                check_count=1,
                depth_count=1,
                stock_external=TimingDistribution((1,), 1, 0),
                instrumented_external=TimingDistribution((1,), 1, 0),
                external_overhead=TimingDistribution((0,), 0, 0),
                instrumented_internal=TimingDistribution((1,), 1, 0),
                array_envelope=TimingDistribution((0,), 0, 0),
                non_array_residual=TimingDistribution((1,), 1, 0),
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
            observed: list[Path] = []

            def compare(capture_dir, *args, **kwargs):
                observed.append(capture_dir)
                return report

            entries = compare_garden_suite(
                raw_path,
                root / "comparisons",
                {},
                warmups=0,
                repetitions=1,
                timeout_seconds=5,
                downloaded_capture_root=capture_root,
                compare=compare,
            )

            self.assertEqual(observed, [capture.resolve()])
            self.assertEqual(entries[0]["comparison_status"], "completed")

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
