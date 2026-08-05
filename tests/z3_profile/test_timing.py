from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from tools.z3_profile import time_stock_replay


FAKE_SOLVER = """#!/usr/bin/env python3
import sys

checks = 0
for line in sys.stdin:
    if line.strip() == "(check-sat)":
        checks += 1
        print("sat" if checks == 1 else "unsat", flush=True)
    elif line.strip() == "(exit)":
        raise SystemExit(0)
"""


class TimingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.solver = self.root / "stock z3"
        self.solver.write_text(FAKE_SOLVER)
        self.solver.chmod(0o755)
        self.capture = self._capture()
        self.manifest = {
            "builds": {
                "stock": {"binary": str(self.solver)},
                "instrumented": {"binary": str(self.solver)},
            }
        }

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_warmups_are_discarded_and_depths_sum_each_repetition(self) -> None:
        clock_values = [
            0,
            1,
            10,
            20,
            100,
            110,
            200,
            220,
            300,
            330,
            400,
            440,
        ]
        with patch(
            "tools.z3_profile.runner.time.perf_counter_ns",
            side_effect=clock_values,
        ):
            report = time_stock_replay(
                self.capture,
                self.manifest,
                warmups=1,
                repetitions=2,
            )

        self.assertEqual(report.checks[0].timing.samples_ns, (10, 30))
        self.assertEqual(report.checks[0].timing.median_ns, 20)
        self.assertEqual(report.checks[0].timing.mad_ns, 10)
        self.assertEqual(report.checks[1].timing.samples_ns, (20, 40))
        self.assertEqual(report.depths[0].timing.samples_ns, (30, 70))
        self.assertEqual(report.depths[0].timing.median_ns, 50)
        self.assertEqual(report.depths[0].timing.mad_ns, 20)
        self.assertEqual(report.depths[0].refinement_ids, (1, 2))
        self.assertEqual(report.depths[0].refinement_steps, (0, 1))
        self.assertEqual(report.depths[0].instances_total, 2)
        self.assertEqual(report.depths[0].instances_added, 2)
        self.assertEqual(report.checks[1].instances_total, 2)
        self.assertEqual(report.checks[1].instances_added_since_previous_check, 2)

    def test_time_command_writes_machine_and_human_reports(self) -> None:
        build_dir = self.root / "z3 build"
        build_dir.mkdir()
        (build_dir / "manifest.json").write_text(json.dumps(self.manifest))
        output = self.root / "stock timing.json"

        completed = subprocess.run(
            [
                sys.executable,
                "tools/z3_array_probe.py",
                "time",
                "--capture-dir",
                str(self.capture),
                "--z3-build-dir",
                str(build_dir),
                "--warmups",
                "0",
                "--repetitions",
                "2",
                "--output",
                str(output),
            ],
            cwd=Path(__file__).resolve().parents[2],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("stock timing: 2 repetitions after 0 warmups", completed.stdout)
        payload = json.loads(output.read_text())
        self.assertEqual(payload["repetitions"], 2)
        self.assertEqual(len(payload["checks"][0]["timing"]["samples_ns"]), 2)

    def _capture(self) -> Path:
        capture = self.root / "capture"
        capture.mkdir()
        transcript = bytearray()
        checks = []
        for check_id, result in enumerate(("sat", "unsat")):
            setup_start = len(transcript)
            if check_id == 0:
                transcript.extend(b"(set-option :print-success false)\n")
                transcript.extend(b"(set-logic QF_LIA)\n")
            else:
                transcript.extend(b"(assert marker_1)\n")
            check_start = len(transcript)
            transcript.extend(b"(check-sat)\n")
            check_end = len(transcript)
            post_end = len(transcript)
            checks.append(
                {
                    "check_id": check_id,
                    "depth": 0,
                    "refinement_id": check_id + 1,
                    "refinement_step": check_id,
                    "setup_byte_start": setup_start,
                    "check_byte_start": check_start,
                    "check_byte_end": check_end,
                    "post_check_byte_end": post_end,
                    "command_ordinal": check_id,
                    "expected_result": result,
                }
            )

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
                            "instances_total": 0 if check["check_id"] == 0 else 2,
                            "instances_added_since_previous_check": (
                                0 if check["check_id"] == 0 else 2
                            ),
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
