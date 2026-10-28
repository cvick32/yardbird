import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

import replay_request


class ReplayRequestTests(unittest.TestCase):
    def fixture(self, root):
        source = root / "original.jsonl"
        payload = {"model": "jev-latest", "questions": {}, "state": {"terms": ["a", "b"]}}
        source.write_text(json.dumps({"event": "request", "query_id": 7, "request": payload}) + "\n")
        return source, payload

    def test_dry_run_preserves_payload_and_never_connects(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, payload = self.fixture(root)
            with patch.object(replay_request.http.client, "HTTPSConnection") as connection:
                replay_request.replay(source, 7, root / "replay.jsonl")
            connection.assert_not_called()
            self.assertEqual(json.loads((root / "replay.jsonl").read_text())["request"], payload)

    def test_error_body_is_retained_and_credential_redacted_without_retry(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, payload = self.fixture(root)
            connection = Mock()
            response = connection.getresponse.return_value
            response.status = 422
            response.read.return_value = b'{"detail":"too many choices; fake-secret"}'
            response.getheader.return_value = "request-123"
            with patch.object(replay_request, "load_dotenv"), patch.dict("os.environ", {"JEV_API_KEY": "fake-secret"}), patch.object(replay_request.http.client, "HTTPSConnection", return_value=connection):
                result = replay_request.replay(source, 7, root / "replay.jsonl", live=True)
            self.assertEqual(result["status"], 422)
            self.assertIn("too many choices", result["body"])
            self.assertNotIn("fake-secret", (root / "replay.jsonl").read_text())
            self.assertIsNone(result["estimated_usd"])
            self.assertEqual(json.loads(connection.request.call_args.args[2]), payload)
            connection.request.assert_called_once()
            connection.close.assert_called_once()

    def test_existing_output_is_rejected_before_connecting(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, _ = self.fixture(root)
            output = root / "replay.jsonl"
            output.write_text("preserve")
            with patch.object(replay_request.http.client, "HTTPSConnection") as connection:
                with self.assertRaises(FileExistsError):
                    replay_request.replay(source, 7, output)
            connection.assert_not_called()
            self.assertEqual(output.read_text(), "preserve")

    def test_missing_query_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            source, _ = self.fixture(Path(directory))
            with self.assertRaises(ValueError):
                replay_request.read_request(source, 8)
