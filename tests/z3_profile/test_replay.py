from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from tools.z3_profile import LoadedCapture, ReplayError, ReplayRunner, replay_build_pair


FAKE_SOLVER = """#!/usr/bin/env python3
import sys
import time
from pathlib import Path

path = Path(__file__)
mode = path.with_suffix(".mode").read_text().strip()
path.with_suffix(".started").touch()
checks = 0
for line in sys.stdin:
    if line.strip() == "(check-sat)":
        checks += 1
        if mode == "slow":
            time.sleep(1)
        result = "sat" if mode == "mismatch" or checks == 1 else "unsat"
        print(result, flush=True)
    elif line.strip() == "(exit)":
        raise SystemExit(0)
"""


class ReplayTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_replays_each_capture_through_both_persistent_processes(self) -> None:
        capture = self._capture(["sat", "unsat"])
        stock = self._solver("persistent", "stock z3")
        instrumented = self._solver("persistent", "instrumented z3")

        replay = replay_build_pair(capture, self._builder_manifest(stock, instrumented))

        self.assertEqual(replay.expected, ("sat", "unsat"))
        self.assertEqual(replay.stock.results, replay.expected)
        self.assertEqual(replay.instrumented.results, replay.expected)

    def test_public_capture_and_runner_interfaces_compose(self) -> None:
        capture = LoadedCapture.load(self._capture(["sat", "unsat"]))
        stock = self._solver("persistent", "stock z3")

        replay = ReplayRunner(stock, label="stock").run(capture)

        self.assertEqual(replay.results, capture.expected_results)
        self.assertEqual(len(replay.timings_ns), 2)

    def test_mismatch_identifies_the_solver_and_check(self) -> None:
        capture = self._capture(["sat", "unsat"])
        stock = self._solver("persistent", "stock-z3")
        instrumented = self._solver("mismatch", "instrumented-z3")

        with self.assertRaisesRegex(
            ReplayError,
            "instrumented: check 1 expected unsat, observed sat",
        ):
            replay_build_pair(capture, self._builder_manifest(stock, instrumented))

    def test_rejects_a_corrupt_index_before_starting_a_solver(self) -> None:
        capture = self._capture(["sat", "unsat"])
        index_path = capture / "solver-session.index.json"
        index = json.loads(index_path.read_text())
        index["checks"][1]["setup_byte_start"] += 1
        index_path.write_text(json.dumps(index))
        stock = self._solver("persistent", "stock-z3")
        instrumented = self._solver("persistent", "instrumented-z3")

        with self.assertRaisesRegex(ReplayError, "invalid byte boundaries"):
            replay_build_pair(capture, self._builder_manifest(stock, instrumented))

        self.assertFalse(stock.with_suffix(".started").exists())
        self.assertFalse(instrumented.with_suffix(".started").exists())

    def test_a_stuck_solver_fails_with_a_bounded_check_timeout(self) -> None:
        capture = self._capture(["sat"])
        stock = self._solver("slow", "stock-z3")
        instrumented = self._solver("persistent", "instrumented-z3")

        with self.assertRaisesRegex(ReplayError, "stock: check 0 timed out"):
            replay_build_pair(
                capture,
                self._builder_manifest(stock, instrumented),
                timeout_seconds=0.05,
            )

    def test_cli_accepts_z3_builder_json_on_stdin(self) -> None:
        capture = self._capture(["sat", "unsat"], "capture with spaces")
        stock = self._solver("persistent", "stock z3")
        instrumented = self._solver("persistent", "instrumented z3")

        completed = self._run_cli(
            capture,
            input_text=json.dumps(self._builder_manifest(stock, instrumented)),
        )

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(
            completed.stdout.splitlines(),
            [
                "expected:     sat unsat",
                "stock:        sat unsat",
                "instrumented: sat unsat",
            ],
        )

    def test_cli_can_rerun_an_existing_z3_builder_directory(self) -> None:
        capture = self._capture(["sat", "unsat"])
        stock = self._solver("persistent", "stock-z3")
        instrumented = self._solver("persistent", "instrumented-z3")
        build_dir = self.root / "z3 build"
        build_dir.mkdir()
        (build_dir / "manifest.json").write_text(
            json.dumps(self._builder_manifest(stock, instrumented))
        )

        completed = self._run_cli(capture, build_dir=build_dir)

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("instrumented: sat unsat", completed.stdout)

    def _run_cli(
        self,
        capture: Path,
        *,
        build_dir: Path | None = None,
        input_text: str | None = None,
    ) -> subprocess.CompletedProcess[str]:
        command = [
            sys.executable,
            "tools/z3_array_probe.py",
            "replay",
            "--capture-dir",
            str(capture),
        ]
        if build_dir is not None:
            command.extend(["--z3-build-dir", str(build_dir)])
        return subprocess.run(
            command,
            cwd=Path(__file__).resolve().parents[2],
            input=input_text,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )

    def _solver(self, mode: str, name: str) -> Path:
        solver = self.root / name
        solver.write_text(FAKE_SOLVER)
        solver.chmod(0o755)
        solver.with_suffix(".mode").write_text(mode)
        return solver

    @staticmethod
    def _builder_manifest(stock: Path, instrumented: Path) -> dict:
        return {
            "builds": {
                "stock": {"binary": str(stock)},
                "instrumented": {"binary": str(instrumented)},
            }
        }

    def _capture(self, results: list[str], name: str = "capture") -> Path:
        capture = self.root / name
        capture.mkdir()
        transcript = bytearray()
        checks = []
        for check_id, result in enumerate(results):
            setup_start = len(transcript)
            if check_id == 0:
                transcript.extend(b"(set-option :print-success false)\n")
                transcript.extend(b"(set-logic QF_LIA)\n")
            else:
                transcript.extend(f"(assert marker_{check_id})\n".encode())
            transcript.extend(f"; yardbird check {check_id} begin\n".encode())
            check_start = len(transcript)
            transcript.extend(b"(check-sat)\n")
            check_end = len(transcript)
            transcript.extend(f"; yardbird check {check_id} result {result}\n".encode())
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
