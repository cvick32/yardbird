from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from tools.z3_profile import compare_capture


FAKE_Z3 = """#!/usr/bin/env python3
import json
import sys
from pathlib import Path

profile_arg = next(
    (arg for arg in sys.argv if arg.startswith("smt.array.profile_output=")),
    None,
)
profile = Path(profile_arg.split("=", 1)[1]).open("w") if profile_arg else None
checks = 0
for line in sys.stdin:
    if line.strip() == "(check-sat)":
        result = "sat" if checks == 0 else "unsat"
        print(result, flush=True)
        if profile:
            profile.write(json.dumps({
                "check_ordinal": checks,
                "result": result,
                "check_elapsed_ns": 100 if checks == 0 else 200,
                "array_envelope_ns": 40 if checks == 0 else 50,
            }) + "\\n")
            profile.flush()
        checks += 1
    elif line.strip() == "(exit)":
        break
if profile:
    profile.close()
"""


class ComparisonTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.stock = self._solver("stock-z3")
        self.instrumented = self._solver("instrumented-z3")
        self.capture = self._capture()
        self.manifest = {
            "builds": {
                "stock": {"binary": str(self.stock)},
                "instrumented": {"binary": str(self.instrumented)},
            }
        }

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_joins_stock_array_and_residual_samples_by_depth(self) -> None:
        with patch(
            "tools.z3_profile.timing.time.perf_counter_ns",
            side_effect=[
                0,
                10,
                20,
                40,
                300,
                350,
                400,
                460,
                500,
                555,
                600,
                665,
                100,
                130,
                200,
                240,
            ],
        ):
            report = compare_capture(
                self.capture,
                self.manifest,
                warmups=0,
                repetitions=2,
            )

        self.assertEqual(report.checks[0].stock_external_samples_ns, (10, 30))
        self.assertEqual(
            report.checks[0].instrumented_internal_samples_ns, (100, 100)
        )
        self.assertEqual(
            report.checks[0].instrumented_external_samples_ns, (50, 55)
        )
        self.assertEqual(report.checks[0].array_envelope_samples_ns, (40, 40))
        self.assertEqual(
            report.checks[0].non_array_residual_samples_ns, (60, 60)
        )
        self.assertEqual(report.depths[0].stock_external_samples_ns, (30, 70))
        self.assertEqual(
            report.depths[0].instrumented_internal_samples_ns, (300, 300)
        )
        self.assertEqual(
            report.depths[0].instrumented_external_samples_ns, (110, 120)
        )
        self.assertEqual(report.depths[0].array_envelope_samples_ns, (90, 90))
        self.assertEqual(
            report.depths[0].non_array_residual_samples_ns, (210, 210)
        )
        self.assertEqual(report.aggregate.check_count, 2)
        self.assertEqual(report.aggregate.depth_count, 1)
        self.assertEqual(report.aggregate.stock_external_samples_ns, (30, 70))
        self.assertEqual(
            report.aggregate.instrumented_external_samples_ns, (110, 120)
        )
        self.assertEqual(report.aggregate.array_envelope_samples_ns, (90, 90))
        self.assertEqual(report.aggregate.external_overhead_samples_ns, (80, 50))
        self.assertEqual(report.aggregate.external_overhead_median_ns, 65)
        self.assertEqual(report.aggregate.external_overhead_mad_ns, 15)
        self.assertIn("aggregate: checks=2 depths=1", report.summary())
        self.assertIn("check_ids=0,1", report.summary())

    def _solver(self, name: str) -> Path:
        solver = self.root / name
        solver.write_text(FAKE_Z3)
        solver.chmod(0o755)
        return solver

    def _capture(self) -> Path:
        capture = self.root / "capture"
        capture.mkdir()
        transcript = bytearray(b"(set-option :print-success false)\n")
        checks = []
        prior_end = 0
        for check_id, result in enumerate(("sat", "unsat")):
            check_start = len(transcript)
            transcript.extend(b"(check-sat)\n")
            check_end = len(transcript)
            checks.append(
                {
                    "check_id": check_id,
                    "depth": 0,
                    "refinement_id": check_id + 1,
                    "refinement_step": check_id,
                    "setup_byte_start": prior_end,
                    "check_byte_start": check_start,
                    "check_byte_end": check_end,
                    "post_check_byte_end": check_end,
                    "command_ordinal": check_id,
                    "expected_result": result,
                }
            )
            prior_end = check_end
        (capture / "solver-session.smt2").write_bytes(transcript)
        (capture / "solver-session.index.json").write_text(
            json.dumps({"checks": checks})
        )
        (capture / "yardbird-profile.json").write_text(
            json.dumps(
                {
                    "solver_checks": [
                        {
                            "check_id": check["check_id"],
                            "depth": check["depth"],
                            "refinement_id": check["refinement_id"],
                            "refinement_step": check["refinement_step"],
                            "result": check["expected_result"],
                            "instances_total": check["check_id"],
                            "instances_added_since_previous_check": check[
                                "check_id"
                            ],
                        }
                        for check in checks
                    ]
                }
            )
        )
        (capture / "manifest.json").write_text(
            json.dumps(
                {
                    "complete": True,
                    "check_count": len(checks),
                    "transcript": "solver-session.smt2",
                    "index": "solver-session.index.json",
                    "profile": "yardbird-profile.json",
                }
            )
        )
        return capture


if __name__ == "__main__":
    unittest.main()
