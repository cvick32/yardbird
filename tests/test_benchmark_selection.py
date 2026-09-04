from __future__ import annotations

import json
import tempfile
import unittest
from argparse import Namespace
from pathlib import Path
from unittest.mock import patch

from yardbird_eval.benchmark_selection import (
    auxiliary_synthesis_config,
    garden_filter_args,
    garden_run_args,
    select_difficult_benchmarks,
    select_formula_research_cohort,
)


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload))


def strategy_result(
    strategy: str,
    run_time: int,
    outcome: dict,
    *,
    cost_function: str = "bmc-cost",
) -> dict:
    return {
        "strategy": strategy,
        "cost_function": cost_function,
        "run_time": run_time,
        "result": outcome,
    }


class DifficultBenchmarkSelectionTests(unittest.TestCase):
    def test_selects_slow_or_timed_out_bmc_and_concrete_results(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            suite_path = Path(temporary) / "results.json"
            write_json(
                suite_path,
                {
                    "benchmarks": [
                        {
                            "example": (
                                "deep-abstract_d50_examples/array/slow-abstract.vmt"
                            ),
                            "result": [
                                strategy_result("abstract", 30_001, {"Success": {}})
                            ],
                        },
                        {
                            "example": "examples/array/timed-out-concrete.vmt",
                            "result": [
                                strategy_result("concrete", 1_000, {"Timeout": 1_000})
                            ],
                        },
                        {
                            "example": "examples/array/not-bmc-cost.vmt",
                            "result": [
                                strategy_result(
                                    "abstract",
                                    90_000,
                                    {"Success": {}},
                                    cost_function="ast-size",
                                )
                            ],
                        },
                        {
                            "example": "examples/array/exactly-threshold.vmt",
                            "result": [
                                strategy_result("concrete", 30_000, {"Success": {}})
                            ],
                        },
                    ]
                },
            )

            selection = select_difficult_benchmarks(str(suite_path), 30)

            self.assertEqual(
                selection["benchmarks"],
                [
                    "examples/array/slow-abstract.vmt",
                    "examples/array/timed-out-concrete.vmt",
                ],
            )
            self.assertEqual(
                selection["reasons"]["examples/array/slow-abstract.vmt"],
                ["abstract-bmc-cost"],
            )
            self.assertEqual(
                selection["reasons"]["examples/array/timed-out-concrete.vmt"],
                ["concrete"],
            )

    def test_run_id_reads_downloaded_subrun_results(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            benchmark_root = Path(temporary)
            run_dir = benchmark_root / "baseline-run"
            suite_path = run_dir / "raw" / "deep-concrete" / "results.json"
            write_json(
                suite_path,
                {
                    "benchmarks": [
                        {
                            "example": "examples/array/hard.vmt",
                            "result": [
                                strategy_result("concrete", 45_000, {"Success": {}})
                            ],
                        }
                    ]
                },
            )
            write_json(
                run_dir / "run.json",
                {"subruns": [{"result_path": str(suite_path)}]},
            )

            with patch(
                "yardbird_eval.benchmark_selection.BENCHMARK_ROOT", benchmark_root
            ):
                selection = select_difficult_benchmarks("baseline-run")

            self.assertEqual(selection["source"], "baseline-run")
            self.assertEqual(selection["benchmarks"], ["examples/array/hard.vmt"])

    def test_auto_uses_newest_downloaded_run_with_both_baselines(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            benchmark_root = Path(temporary)
            for run_id, started_at, strategies in [
                ("older-complete", "2026-01-01", ["abstract", "concrete"]),
                ("newer-incomplete", "2026-02-01", ["abstract"]),
            ]:
                run_dir = benchmark_root / run_id
                suite_path = run_dir / "raw" / "results.json"
                results = [
                    strategy_result(strategy, 31_000, {"Success": {}})
                    for strategy in strategies
                ]
                write_json(
                    suite_path,
                    {
                        "benchmarks": [
                            {
                                "example": f"examples/array/{run_id}.vmt",
                                "result": results,
                            }
                        ]
                    },
                )
                write_json(
                    run_dir / "run.json",
                    {
                        "started_at": started_at,
                        "benchmark_types": (
                            ["deep-abstract", "deep-concrete"]
                            if run_id == "older-complete"
                            else ["deep-abstract"]
                        ),
                        "subruns": [{"result_path": str(suite_path)}],
                    },
                )

            with patch(
                "yardbird_eval.benchmark_selection.BENCHMARK_ROOT", benchmark_root
            ):
                selection = select_difficult_benchmarks("auto")

            self.assertEqual(selection["source"], "older-complete")

    def test_garden_filter_args_preserve_selection_limit_and_seed(self) -> None:
        args = Namespace(
            benchmark_selection={
                "benchmarks": ["examples/array/one.vmt", "examples/array/two.vmt"]
            },
            limit=1,
            sample_seed=7,
        )

        self.assertEqual(
            garden_filter_args(args),
            [
                "--include",
                "examples/array/one.vmt",
                "--include",
                "examples/array/two.vmt",
                "--limit",
                "1",
                "--sample-seed",
                "7",
            ],
        )

    def test_garden_run_args_include_auxiliary_synthesis_settings(self) -> None:
        args = Namespace(
            benchmark_selection=None,
            limit=None,
            sample_seed=None,
            synthesis_trigger="repeated-pattern",
            synthesis_guard_policy="interpolant",
            synthesis_after=None,
            synthesis_refinement_limit_window=None,
            synthesis_repeated_pattern_threshold=3,
        )

        self.assertEqual(
            auxiliary_synthesis_config(args),
            {
                "trigger": "repeated-pattern",
                "guard_policy": "interpolant",
                "after": None,
                "refinement_limit_window": None,
                "repeated_pattern_threshold": 3,
            },
        )
        self.assertEqual(
            garden_run_args(args),
            [
                "--synthesis-trigger",
                "repeated-pattern",
                "--synthesis-guard-policy",
                "interpolant",
                "--synthesis-repeated-pattern-threshold",
                "3",
            ],
        )

    def test_formula_research_cohort_combines_fixed_and_dynamic_cases(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            suite_path = root / "results.json"
            cohort_path = root / "formula-cohort.json"
            write_json(
                cohort_path,
                {
                    "existing-yardbird-hard-tail-wins": [
                        "examples/array/known-win.vmt"
                    ],
                    "abstract-z3-regressions": [
                        "examples/array/known-regression.vmt"
                    ],
                },
            )
            write_json(
                suite_path,
                {
                    "benchmarks": [
                        {
                            "example": "examples/array/concrete-only-win.vmt",
                            "result": [
                                strategy_result("concrete", 1_000, {"Success": {}}),
                                strategy_result("abstract", 120_000, {"Timeout": 120_000}),
                            ],
                        },
                        {
                            "example": "examples/array/both-succeed.vmt",
                            "result": [
                                strategy_result("concrete", 1_000, {"Success": {}}),
                                strategy_result("abstract", 2_000, {"Success": {}}),
                            ],
                        },
                    ]
                },
            )

            with patch(
                "yardbird_eval.benchmark_selection.FORMULA_RESEARCH_COHORT",
                cohort_path,
            ):
                selection = select_formula_research_cohort(str(suite_path))

            self.assertEqual(
                selection["benchmarks"],
                [
                    "examples/array/concrete-only-win.vmt",
                    "examples/array/known-regression.vmt",
                    "examples/array/known-win.vmt",
                ],
            )
            self.assertEqual(
                selection["reasons"]["examples/array/concrete-only-win.vmt"],
                ["concrete-success-yardbird-timeout"],
            )


if __name__ == "__main__":
    unittest.main()
