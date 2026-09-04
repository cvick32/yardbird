from __future__ import annotations

import io
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from yardbird_eval.aws_backend import (
    extract_capture_archive,
    read_user_data,
    refresh_aws_run,
)
from yardbird_eval.common import STATUS_COMPLETED, STATUS_RUNNING


class RefreshAwsRunTests(unittest.TestCase):
    @patch("yardbird_eval.aws_backend.save_manifest")
    @patch("yardbird_eval.aws_backend.describe_instance_state", return_value=None)
    @patch("yardbird_eval.aws_backend.s3_object_exists", return_value=False)
    def test_completed_subrun_stays_completed_when_remote_resources_disappear(
        self,
        object_exists,
        describe_instance_state,
        save_manifest,
    ) -> None:
        completed_at = "2026-07-20T09:13:42-05:00"
        manifest = {
            "status": STATUS_COMPLETED,
            "completed_at": completed_at,
            "progress": {
                "completed": 1,
                "failed": 0,
                "running": 0,
                "total": 1,
            },
            "subruns": [
                {
                    "status": STATUS_COMPLETED,
                    "completed_at": completed_at,
                    "bucket": "yardbird-benchmarks",
                    "region": "us-east-2",
                    "s3_prefix": "benchmarks/deep-run",
                    "instance_id": "i-completed",
                }
            ],
        }

        refresh_aws_run(manifest)

        self.assertEqual(manifest["status"], STATUS_COMPLETED)
        self.assertEqual(manifest["subruns"][0]["status"], STATUS_COMPLETED)
        self.assertEqual(manifest["subruns"][0]["completed_at"], completed_at)
        self.assertEqual(
            manifest["progress"],
            {
                "completed": 1,
                "failed": 0,
                "running": 0,
                "total": 1,
            },
        )
        object_exists.assert_not_called()
        describe_instance_state.assert_not_called()
        save_manifest.assert_called_once_with(manifest)


class CaptureArchiveTests(unittest.TestCase):
    def test_worker_capture_switch_is_rendered_explicitly(self) -> None:
        ordinary = read_user_data("deep-concrete", "ordinary", "bucket")
        captured = read_user_data(
            "deep-concrete",
            "captured",
            "bucket",
            capture_solver_journals=True,
        )

        self.assertIn('if [ "false" = "true" ]; then', ordinary)
        self.assertIn('if [ "true" = "true" ]; then', captured)

    def test_benchmark_filters_are_rendered_as_worker_arguments(self) -> None:
        rendered = read_user_data(
            "deep-concrete",
            "filtered",
            "bucket",
            garden_args=[
                "--include",
                "examples/array/hard.vmt",
                "--limit",
                "1",
            ],
        )

        self.assertIn(
            "garden_args=(--include examples/array/hard.vmt --limit 1)",
            rendered,
        )

    def test_auxiliary_synthesis_arguments_are_rendered_for_the_worker(self) -> None:
        rendered = read_user_data(
            "array-best-depth50",
            "auxiliary",
            "bucket",
            garden_args=[
                "--synthesis-trigger",
                "non-local",
                "--synthesis-guard-policy",
                "interpolant",
            ],
        )

        self.assertIn(
            "garden_args=(--synthesis-trigger non-local "
            "--synthesis-guard-policy interpolant)",
            rendered,
        )
        self.assertIn('"${garden_args[@]}"', rendered)
        self.assertIn("openjdk-17-jre-headless", rendered)

    def test_worker_updates_main_and_uses_the_selected_repository_config(self) -> None:
        rendered = read_user_data(
            "protocols",
            "latest-main",
            "bucket",
            benchmark_config_path="garden/new_benchmarks_aws_config.yaml",
        )

        self.assertIn("git checkout main", rendered)
        self.assertIn("git pull --ff-only origin main", rendered)
        self.assertIn(
            "benchmark_config_path=garden/new_benchmarks_aws_config.yaml",
            rendered,
        )
        self.assertIn('--config "$benchmark_config_path"', rendered)
        self.assertNotIn("git checkout --detach", rendered)

    def test_capture_archive_is_extracted_under_matrix_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            archive_path = root / "captures.tar.gz"
            payload = b"(check-sat)\n"
            with tarfile.open(archive_path, "w:gz") as archive:
                member = tarfile.TarInfo("0000/0007/solver-session.smt2")
                member.size = len(payload)
                archive.addfile(member, io.BytesIO(payload))

            capture_root = root / "captures" / "deep-abstract"
            extract_capture_archive(archive_path, capture_root)

            self.assertEqual(
                (capture_root / "0000" / "0007" / "solver-session.smt2").read_bytes(),
                payload,
            )

    def test_capture_archive_rejects_path_escape(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            archive_path = root / "captures.tar.gz"
            with tarfile.open(archive_path, "w:gz") as archive:
                member = tarfile.TarInfo("../escaped.smt2")
                member.size = 0
                archive.addfile(member, io.BytesIO())

            with self.assertRaisesRegex(RuntimeError, "escapes destination"):
                extract_capture_archive(archive_path, root / "captures")

    @patch("yardbird_eval.aws_backend.save_manifest")
    @patch("yardbird_eval.aws_backend.describe_instance_state", return_value=None)
    @patch("yardbird_eval.aws_backend.s3_object_exists", return_value=False)
    def test_downloaded_subrun_recovers_from_stale_running_status(
        self,
        object_exists,
        describe_instance_state,
        save_manifest,
    ) -> None:
        completed_at = "2026-07-20T09:13:42-05:00"
        manifest = {
            "status": STATUS_RUNNING,
            "completed_at": completed_at,
            "progress": {
                "completed": 0,
                "failed": 0,
                "running": 1,
                "total": 1,
            },
            "subruns": [
                {
                    "status": STATUS_RUNNING,
                    "completed_at": completed_at,
                    "downloaded_at": "2026-07-20T09:13:51-05:00",
                    "bucket": "yardbird-benchmarks",
                    "region": "us-east-2",
                    "s3_prefix": "benchmarks/deep-run",
                    "instance_id": "i-completed",
                }
            ],
        }

        refresh_aws_run(manifest)

        self.assertEqual(manifest["status"], STATUS_COMPLETED)
        self.assertEqual(manifest["subruns"][0]["status"], STATUS_COMPLETED)
        self.assertEqual(manifest["subruns"][0]["completed_at"], completed_at)
        self.assertEqual(manifest["progress"]["completed"], 1)
        self.assertEqual(manifest["progress"]["running"], 0)
        object_exists.assert_not_called()
        describe_instance_state.assert_not_called()
        save_manifest.assert_called_once_with(manifest)


if __name__ == "__main__":
    unittest.main()
