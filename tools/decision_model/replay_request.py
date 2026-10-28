#!/usr/bin/env python3
"""Replay one logged JEV request, preserving HTTP error bodies. Offline by default."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import http.client
import json
import os
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from yardbird_eval.common import load_dotenv  # noqa: E402


def read_request(path, query_id):
    matches = []
    with path.open() as stream:
        for line in stream:
            if not line.strip():
                continue
            record = json.loads(line)
            if record.get("event") == "request" and record.get("query_id") == query_id:
                matches.append(record)
    if len(matches) != 1:
        raise ValueError(f"Expected exactly one request for query {query_id}; found {len(matches)}")
    return matches[0]


def replay(source, query_id, output, *, live=False, timeout=30):
    original = read_request(source, query_id)
    request = original["request"]
    body = json.dumps(request, separators=(",", ":"), ensure_ascii=False,
                      sort_keys=True, allow_nan=False).encode()
    key = ""
    if live:
        load_dotenv()
        key = os.environ.get("JEV_API_KEY", "").strip()
        if not key:
            raise ValueError("Set JEV_API_KEY in the environment or repository .env")
    # Reserve the evidence file before making any billable request.
    with output.open("x") as stream:
        def record(value):
            serialized = json.dumps(value, ensure_ascii=False)
            if key:
                serialized = serialized.replace(key, "[REDACTED]")
            stream.write(serialized + "\n")
            stream.flush()

        record({"event": "replay_request", "timestamp": datetime.now(timezone.utc).isoformat(),
                "source": str(source.resolve()), "query_id": query_id,
                "original_configuration": original.get("configuration"),
                "original_stage": original.get("stage"), "original_depth": original.get("depth"),
                "request_sha256": hashlib.sha256(body).hexdigest(), "request_bytes": len(body),
                "live": live, "timeout_secs": timeout, "request": request})
        if not live:
            return {"event": "dry_run", "request_bytes": len(body)}
        connection = http.client.HTTPSConnection("api.typesafe.ai", timeout=timeout)
        started = time.monotonic()
        try:
            connection.request("POST", "/v1/systemone", body,
                               {"Authorization": "Bearer " + key, "Content-Type": "application/json"})
            response = connection.getresponse()
            raw = response.read(4 * 1024 * 1024 + 1)
            truncated = len(raw) > 4 * 1024 * 1024
            text = raw[:4 * 1024 * 1024].decode(errors="replace").replace(key, "[REDACTED]")
            try:
                parsed = json.loads(text)
            except ValueError:
                parsed = None
            usage = parsed.get("usage", {}) if isinstance(parsed, dict) else {}
            config = original.get("configuration", {})
            estimated = None
            input_tokens, output_tokens = usage.get("input_tokens"), usage.get("output_tokens")
            input_rate, output_rate = config.get("jev_input_usd_per_million"), config.get("jev_output_usd_per_million")
            if output_tokens is None and output_rate == 0:
                output_tokens = 0
            if (type(input_tokens) is int and input_tokens >= 0
                    and type(output_tokens) is int and output_tokens >= 0
                    and input_rate is not None and output_rate is not None):
                estimated = (input_tokens * input_rate + output_tokens * output_rate) / 1_000_000
            result = {"event": "replay_response", "status": response.status,
                      "elapsed_secs": time.monotonic() - started,
                      "request_id": response.getheader("x-request-id"),
                      "body": text, "body_truncated": truncated,
                      "usage": usage, "estimated_usd": estimated}
            record(result)
            return result
        except Exception as error:
            result = {"event": "transport_error", "error": str(error).replace(key, "[REDACTED]"),
                      "elapsed_secs": time.monotonic() - started, "estimated_usd": None}
            record(result)
            raise
        finally:
            connection.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--query-id", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True, help="New JSONL evidence file")
    parser.add_argument("--live", action="store_true", help="Make exactly one API call")
    parser.add_argument("--timeout-secs", type=float, default=30)
    args = parser.parse_args()
    if args.timeout_secs <= 0:
        parser.error("--timeout-secs must be positive")
    result = replay(args.log, args.query_id, args.output, live=args.live, timeout=args.timeout_secs)
    print(json.dumps({k: v for k, v in result.items() if k != "body"}))
