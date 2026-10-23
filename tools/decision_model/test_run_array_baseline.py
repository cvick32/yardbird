import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

import run_array_baseline as runner


class ArrayBaselineTests(unittest.TestCase):
    def args(self, root, baseline="yardbird"):
        return SimpleNamespace(binary=root / "yardbird", examples=root, baseline=baseline,
                               depth=20, timeout_secs=120, grace_secs=10)

    def test_commands_keep_current_jev_configuration_and_separate_ordinary_baseline(self):
        root = Path("/tmp/array-baseline-test")
        jev = runner.command_for(self.args(root, "jev"), root / "example.vmt", root / "case")
        self.assertIn("conditional-binding", jev)
        self.assertIn("property-directed", jev)
        self.assertIn("--jev-batch", jev)
        self.assertEqual(jev[jev.index("-d") + 1], "20")
        self.assertNotIn("--strategy", jev)
        ordinary = runner.command_for(self.args(root), root / "example.vmt", root / "case")
        self.assertNotIn("--jev-log", ordinary)
        self.assertIn("bmc-cost", ordinary)

    def test_structured_failure_is_not_success_even_with_zero_exit(self):
        for reason in ("no_progress", "timeout", "solver_unknown", "refinement_limit", "error"):
            result = {"run_progress": {"termination_reason": reason, "current_depth": 3}}
            outcome, progress = runner.classify(result, None, 0, None, 20)
            self.assertEqual(outcome, reason)
            self.assertEqual(progress["current_depth"], 3)
        complete = {"found_proof": False, "run_progress": {"termination_reason": "depth_limit", "deepest_completed_depth": 19}}
        self.assertEqual(runner.classify(complete, None, 0, None, 20)[0], "bounded_complete")
        complete["run_progress"]["deepest_completed_depth"] = 18
        self.assertEqual(runner.classify(complete, None, 0, None, 20)[0], "incomplete")
        self.assertEqual(runner.classify(None, None, 0, None, 20)[0], "invalid_json")
        self.assertEqual(runner.classify(None, None, -6, None, 20)[0], "process_signal")

    def test_hard_timeout_preserves_checkpoint_and_kills_process_group(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            case = root / "case"
            fake = Mock(pid=12345, returncode=-15)
            fake.wait.side_effect = [subprocess.TimeoutExpired("yardbird", 130), -15]

            def launch(command, **kwargs):
                runner.save_json(case / "progress.json", {"termination_reason": "running", "current_depth": 7, "deepest_completed_depth": 6})
                return fake

            with patch.object(runner.subprocess, "Popen", side_effect=launch), patch.object(runner.os, "killpg") as kill:
                row = runner.run_case(self.args(root), root / "example.vmt", case)
            self.assertEqual(row["outcome"], "hard_timeout")
            self.assertEqual(row["deepest_completed_depth"], 6)
            kill.assert_called_once_with(12345, runner.signal.SIGTERM)
            self.assertEqual(runner.read_json(case / "summary.json")["outcome"], "hard_timeout")

    def test_dry_run_never_starts_yardbird_or_creates_outputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "fake-yardbird"
            binary.write_text("unused")
            binary.chmod(0o755)
            (root / "a.vmt").write_text("fixture")
            output = root / "out"
            with patch.object(runner.subprocess, "Popen") as popen, contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(runner.main(["--binary", str(binary), "--examples", str(root), "--output", str(output), "--dry-run"]), 0)
                popen.assert_not_called()
            self.assertFalse(output.exists())

    def test_resume_skips_interrupted_case_and_continues_without_requerying(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "fake-yardbird"
            binary.write_text("unused")
            binary.chmod(0o755)
            for name in ("a", "b"):
                (root / f"{name}.vmt").write_text("fixture")
            output = root / "out"
            args = ["--binary", str(binary), "--examples", str(root), "--output", str(output), "--baseline", "yardbird"]

            def interrupted(options, benchmark, case):
                case.mkdir(parents=True)
                row = {"benchmark": benchmark.name, "outcome": "interrupted", "artifacts": str(case)}
                runner.save_json(case / "summary.json", row)
                return row

            with patch.object(runner, "run_case", side_effect=interrupted), patch.object(runner.subprocess, "run", return_value=SimpleNamespace(stdout="fixture-commit")), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(runner.main(args), 130)

            def complete(options, benchmark, case):
                case.mkdir(parents=True)
                row = {"benchmark": benchmark.name, "outcome": "bounded_complete", "artifacts": str(case)}
                runner.save_json(case / "summary.json", row)
                return row

            with patch.object(runner, "run_case", side_effect=complete) as run_case, contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(runner.main([*args, "--resume"]), 0)
                self.assertEqual(run_case.call_count, 1)
                self.assertEqual(run_case.call_args.args[1].name, "b.vmt")
            summary = runner.read_json(output / "summary.json")
            self.assertEqual(summary["outcomes"], {"interrupted": 1, "bounded_complete": 1})
            self.assertEqual(summary["remaining"], 0)


if __name__ == "__main__":
    unittest.main()
