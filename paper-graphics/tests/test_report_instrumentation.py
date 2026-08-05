from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from report.instrumentation import build_instrumentation_report


class InstrumentationReportTests(unittest.TestCase):
    def test_completed_comparisons_generate_csv_charts_and_typst(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            summary = root / "comparisons.json"
            summary.write_text(
                json.dumps(
                    {
                        "warmups": 3,
                        "repetitions": 15,
                        "entries": [
                            {
                                "example": "examples/array/array_copy.vmt",
                                "strategy": "concrete",
                                "cost_function": "bmc-cost",
                                "depth": 5,
                                "comparison_status": "completed",
                                "metrics": {
                                    "stock_external_median_ns": 10_000_000,
                                    "instrumented_external_median_ns": 11_000_000,
                                    "external_overhead_median_ns": 1_000_000,
                                    "external_overhead_pct": 10.0,
                                    "instrumented_internal_median_ns": 8_000_000,
                                    "array_envelope_median_ns": 2_000_000,
                                    "non_array_residual_median_ns": 6_000_000,
                                    "array_fraction_pct": 25.0,
                                },
                            }
                        ],
                    }
                )
            )
            manifest = {"instrumentation": {"comparison_summary_path": str(summary)}}

            report = build_instrumentation_report(manifest, root)

            workbook_text = "\n".join(report.sections)
            self.assertIn("Instrumented Z3 Replay Comparison", workbook_text)
            self.assertIn("15 paired repetitions", workbook_text)
            self.assertTrue(Path(report.exports["instrumentation_csv"]).is_file())
            self.assertEqual(len(report.assets), 2)
            for asset in report.assets:
                self.assertTrue(Path(asset).is_file())

    def test_unavailable_comparisons_still_generate_a_report_section(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            summary = root / "comparisons.json"
            summary.write_text(
                json.dumps(
                    {
                        "warmups": 3,
                        "repetitions": 15,
                        "entries": [
                            {
                                "example": "examples/array/slow.vmt",
                                "strategy": "abstract",
                                "cost_function": "bmc-cost",
                                "depth": 5,
                                "yardbird_result_type": "Timeout",
                                "comparison_status": "unavailable",
                                "comparison_error": "Yardbird timed out",
                            }
                        ],
                    }
                )
            )
            manifest = {"instrumentation": {"comparison_summary_path": str(summary)}}

            report = build_instrumentation_report(manifest, root)

            self.assertIn("no paired replay timing", "\n".join(report.sections))
            self.assertEqual(report.assets, [])
            self.assertTrue(Path(report.exports["instrumentation_csv"]).is_file())

    def test_full_runs_aggregate_every_session_by_strategy(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            summary = root / "comparisons.json"
            entries = [
                self._completed_entry(
                    f"examples/array/abstract_{index}.vmt",
                    "abstract",
                    10_000_000 + index,
                )
                for index in range(45)
            ]
            entries.extend(
                self._completed_entry(
                    f"examples/array/concrete_{index}.vmt",
                    "concrete",
                    20_000_000 + index,
                )
                for index in range(5)
            )
            summary.write_text(
                json.dumps({"warmups": 3, "repetitions": 15, "entries": entries})
            )
            manifest = {"instrumentation": {"comparison_summary_path": str(summary)}}

            report = build_instrumentation_report(manifest, root)

            workbook = "\n".join(report.sections)
            external_svg = report.assets[0].read_text()
            self.assertIn("abstract/bmc-cost", workbook)
            self.assertIn("concrete", workbook)
            self.assertIn("45", workbook)
            self.assertIn("5", workbook)
            self.assertIn("abstract/bmc-cost (45 sessions)", external_svg)
            self.assertIn("concrete (5 sessions)", external_svg)

    @staticmethod
    def _completed_entry(example: str, strategy: str, stock_ns: int) -> dict:
        return {
            "example": example,
            "strategy": strategy,
            "cost_function": "bmc-cost",
            "depth": 5,
            "comparison_status": "completed",
            "metrics": {
                "stock_external_median_ns": stock_ns,
                "instrumented_external_median_ns": stock_ns + 1_000_000,
                "external_overhead_median_ns": 1_000_000,
                "external_overhead_pct": 10.0,
                "instrumented_internal_median_ns": 8_000_000,
                "array_envelope_median_ns": 2_000_000,
                "non_array_residual_median_ns": 6_000_000,
                "array_fraction_pct": 25.0,
            },
        }


if __name__ == "__main__":
    unittest.main()
