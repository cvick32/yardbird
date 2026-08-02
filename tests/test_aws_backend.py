from __future__ import annotations

import unittest
from unittest.mock import patch

from yardbird_eval.aws_backend import refresh_aws_run
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
