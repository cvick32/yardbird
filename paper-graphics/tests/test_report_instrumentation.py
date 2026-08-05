from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from report.build_report import instrumentation_workbook_sections


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

            sections, exports = instrumentation_workbook_sections(manifest, root)

            workbook_text = "\n".join(sections)
            self.assertIn("Instrumented Z3 Replay Comparison", workbook_text)
            self.assertIn("15 paired repetitions", workbook_text)
            self.assertTrue(Path(exports["instrumentation_csv"]).is_file())
            self.assertEqual(len(exports["instrumentation_figure_assets"]), 2)
            for asset in exports["instrumentation_figure_assets"]:
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

            sections, exports = instrumentation_workbook_sections(manifest, root)

            self.assertIn("no paired replay timing", "\n".join(sections))
            self.assertEqual(exports["instrumentation_figure_assets"], [])
            self.assertTrue(Path(exports["instrumentation_csv"]).is_file())


if __name__ == "__main__":
    unittest.main()
