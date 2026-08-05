from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from tools.z3_profile import ReplayError, profile_instrumented_replay


FAKE_INSTRUMENTED_Z3 = """#!/usr/bin/env python3
import json
import sys
from pathlib import Path

output_arg = next(arg for arg in sys.argv if arg.startswith("smt.array.profile_output="))
output = Path(output_arg.split("=", 1)[1])
mode = Path(__file__).with_suffix(".mode").read_text().strip()
checks = 0
with output.open("w") as profile:
    for line in sys.stdin:
        if line.strip() != "(check-sat)":
            continue
        result = "sat" if checks == 0 else "unsat"
        print(result, flush=True)
        record = {
            "check_ordinal": checks + (1 if mode == "bad-ordinal" else 0),
            "result": result,
            "check_elapsed_ns": 100 + checks,
            "array_envelope_ns": 25 + checks,
        }
        if mode == "version-label":
            record["schema_version"] = "unwanted"
        profile.write(json.dumps(record) + "\\n")
        profile.flush()
        checks += 1
"""


class InstrumentedReplayTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.capture = self._capture()
        self.stock = self._solver("stock-z3", "ok")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_validates_and_returns_each_instrumented_check(self) -> None:
        instrumented = self._solver("instrumented-z3", "ok")

        replay = profile_instrumented_replay(
            self.capture, self._manifest(instrumented)
        )

        self.assertEqual([check.result for check in replay.checks], ["sat", "unsat"])
        self.assertEqual(replay.checks[0].check_elapsed_ns, 100)
        self.assertEqual(replay.checks[0].array_envelope_ns, 25)
        self.assertGreater(replay.checks[0].external_elapsed_ns, 0)

    def test_rejects_misaligned_ordinals(self) -> None:
        instrumented = self._solver("instrumented-z3", "bad-ordinal")

        with self.assertRaisesRegex(ReplayError, "ordinal does not match"):
            profile_instrumented_replay(
                self.capture, self._manifest(instrumented)
            )

    def test_rejects_profile_version_labels(self) -> None:
        instrumented = self._solver("instrumented-z3", "version-label")

        with self.assertRaisesRegex(ReplayError, "contains version labels"):
            profile_instrumented_replay(
                self.capture, self._manifest(instrumented)
            )

    def _manifest(self, instrumented: Path) -> dict:
        return {
            "builds": {
                "stock": {"binary": str(self.stock)},
                "instrumented": {"binary": str(instrumented)},
            }
        }

    def _solver(self, name: str, mode: str) -> Path:
        solver = self.root / name
        solver.write_text(FAKE_INSTRUMENTED_Z3)
        solver.chmod(0o755)
        solver.with_suffix(".mode").write_text(mode)
        return solver

    def _capture(self) -> Path:
        capture = self.root / "capture"
        capture.mkdir()
        transcript = bytearray(b"(set-option :print-success false)\n")
        checks = []
        prior_end = 0
        for check_id, result in enumerate(("sat", "unsat")):
            setup_start = prior_end
            check_start = len(transcript)
            transcript.extend(b"(check-sat)\n")
            check_end = len(transcript)
            checks.append(
                {
                    "check_id": check_id,
                    "depth": 0,
                    "refinement_id": check_id + 1,
                    "refinement_step": check_id,
                    "setup_byte_start": setup_start,
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
