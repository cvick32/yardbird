from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from yardbird_eval import cli
from yardbird_eval.aws_backend import describe_instance_state, refresh_aws_run
from yardbird_eval.common import CommandError, build_report_for_run
from yardbird_eval.object_store import s3_object_exists


class FinishedAwsReportTests(unittest.TestCase):
    @patch("yardbird_eval.aws_backend.save_manifest")
    @patch("yardbird_eval.aws_backend.describe_instance_state", return_value="shutting-down")
    @patch("yardbird_eval.aws_backend.s3_object_exists", return_value=False)
    def test_report_after_manual_termination(self, exists, state, save):
        manifest = {
            "run_id": "finished", "env": "aws", "status": "RUNNING",
            "subruns": [
                {"status": "COMPLETED", "benchmark_type": "yardbird"},
                {"status": "RUNNING", "benchmark_type": "random-1000",
                 "bucket": "b", "region": "r", "s3_prefix": "p",
                 "instance_id": "i", "requires_completion_marker": True},
            ],
        }
        refresh_aws_run(manifest)
        self.assertEqual(manifest["status"], "FAILED")
        self.assertEqual(manifest["progress"]["running"], 0)
        with patch("yardbird_eval.cli.download_aws_artifacts") as download, patch(
            "yardbird_eval.cli.build_report_for_run"
        ) as report:
            cli.maybe_generate_report(manifest)
        download.assert_called_once_with(manifest)
        report.assert_called_once_with(manifest)

    def test_failed_run_with_running_sibling_cannot_generate_report(self):
        manifest = {"run_id": "active", "status": "FAILED", "subruns": [
            {"status": "FAILED"}, {"status": "RUNNING"}, {"status": "COMPLETED"},
        ]}
        for generate in (cli.maybe_generate_report, build_report_for_run):
            with self.subTest(generate=generate.__name__), self.assertRaises(RuntimeError):
                generate(manifest)

    def test_all_failed_run_has_clear_error(self):
        with self.assertRaisesRegex(RuntimeError, "no completed"):
            cli.maybe_generate_report({"run_id": "empty", "status": "FAILED",
                                       "subruns": [{"status": "FAILED"}]})

    @patch("yardbird_eval.common.run_command")
    def test_report_builder_accepts_terminal_failure(self, command):
        with tempfile.TemporaryDirectory() as directory:
            build_report_for_run({"run_id": "finished", "status": "FAILED",
                                  "run_dir": directory, "manifest_path": str(Path(directory) / "run.json"),
                                  "subruns": [{"status": "COMPLETED"}, {"status": "FAILED"}]})
        command.assert_called_once()

    @patch("yardbird_eval.aws_backend.save_manifest")
    @patch("yardbird_eval.aws_backend.object_store_download")
    def test_download_skips_failed_subrun(self, download, save):
        from yardbird_eval.aws_backend import download_aws_artifacts
        download_aws_artifacts({"subruns": [{"status": "FAILED", "benchmark_type": "random-1000"}]})
        download.assert_not_called()


class AwsLookupErrorTests(unittest.TestCase):
    @patch("yardbird_eval.aws_backend.run_command")
    def test_ec2_connection_failure_is_not_an_unknown_instance(self, command):
        command.return_value = subprocess.CompletedProcess([], 255, "", "Could not connect to the endpoint URL")
        with self.assertRaisesRegex(CommandError, "Could not connect"):
            describe_instance_state("i", "r")

    @patch("yardbird_eval.object_store.run_command")
    def test_s3_lookup_failure_is_not_a_missing_object(self, command):
        command.return_value = subprocess.CompletedProcess([], 255, "", "Could not connect to the endpoint URL")
        with self.assertRaisesRegex(CommandError, "Could not connect"):
            s3_object_exists("b", "k", "r")

    @patch("yardbird_eval.object_store.run_command")
    def test_missing_s3_object_is_false(self, command):
        command.return_value = subprocess.CompletedProcess([], 254, "", "An error occurred (404) when calling the HeadObject operation: Not Found")
        self.assertFalse(s3_object_exists("b", "k", "r"))


if __name__ == "__main__":
    unittest.main()
