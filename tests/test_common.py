from __future__ import annotations

import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from yardbird_eval.common import prefer_aws_dotenv


class PreferAwsDotenvTests(unittest.TestCase):
    def test_project_aws_credentials_replace_ambient_session(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            dotenv = Path(temporary) / ".env"
            dotenv.write_text(
                "AWS_ACCESS_KEY_ID=project-access\n"
                "AWS_SECRET_ACCESS_KEY=project-secret\n"
                "AWS_DEFAULT_REGION=us-east-2\n"
                "DATABASE_URL=project-database\n"
            )
            ambient = {
                "AWS_ACCESS_KEY_ID": "ambient-access",
                "AWS_SECRET_ACCESS_KEY": "ambient-secret",
                "AWS_SESSION_TOKEN": "stale-session",
                "AWS_PROFILE": "ambient-profile",
                "DATABASE_URL": "ambient-database",
            }

            with patch.dict(os.environ, ambient, clear=True):
                changed = prefer_aws_dotenv(dotenv)

                self.assertTrue(changed)
                self.assertEqual(os.environ["AWS_ACCESS_KEY_ID"], "project-access")
                self.assertEqual(os.environ["AWS_SECRET_ACCESS_KEY"], "project-secret")
                self.assertEqual(os.environ["AWS_DEFAULT_REGION"], "us-east-2")
                self.assertNotIn("AWS_SESSION_TOKEN", os.environ)
                self.assertNotIn("AWS_PROFILE", os.environ)
                self.assertEqual(os.environ["DATABASE_URL"], "ambient-database")

    def test_dotenv_without_aws_credentials_leaves_ambient_aws_values_alone(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            dotenv = Path(temporary) / ".env"
            dotenv.write_text("DATABASE_URL=project-database\n")
            ambient = {"AWS_PROFILE": "ambient-profile"}

            with patch.dict(os.environ, ambient, clear=True):
                changed = prefer_aws_dotenv(dotenv)

                self.assertFalse(changed)
                self.assertEqual(os.environ["AWS_PROFILE"], "ambient-profile")


if __name__ == "__main__":
    unittest.main()
