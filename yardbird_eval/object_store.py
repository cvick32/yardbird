from __future__ import annotations

import os
from pathlib import Path

from .common import ensure_dir, run_command


def r2_aws_env() -> dict[str, str] | None:
    access_key = os.environ.get("YARDBIRD_R2_ACCESS_KEY_ID")
    secret_key = os.environ.get("YARDBIRD_R2_SECRET_ACCESS_KEY")
    session_token = os.environ.get("YARDBIRD_R2_SESSION_TOKEN")
    if not access_key or not secret_key:
        return None

    env = os.environ.copy()
    env["AWS_ACCESS_KEY_ID"] = access_key
    env["AWS_SECRET_ACCESS_KEY"] = secret_key
    env["AWS_DEFAULT_REGION"] = os.environ.get("LAB_R2_REGION", "auto")
    if session_token:
        env["AWS_SESSION_TOKEN"] = session_token
    return env


def object_store_head_object(
    bucket: str,
    key: str,
    region: str,
    endpoint_url: str | None = None,
) -> bool:
    command = ["aws"]
    if endpoint_url:
        command.extend(["--endpoint-url", endpoint_url])
    command.extend(
        [
            "s3api",
            "head-object",
            "--bucket",
            bucket,
            "--key",
            key,
            "--region",
            region,
        ]
    )
    result = run_command(command, check=False, env=r2_aws_env() if endpoint_url else None)
    return result.returncode == 0


def object_store_download(
    bucket: str,
    key: str,
    destination: Path,
    region: str,
    endpoint_url: str | None = None,
) -> None:
    ensure_dir(destination.parent)
    command = ["aws"]
    if endpoint_url:
        command.extend(["--endpoint-url", endpoint_url])
    command.extend(
        [
            "s3",
            "cp",
            f"s3://{bucket}/{key}",
            str(destination),
            "--region",
            region,
        ]
    )
    run_command(
        command,
        check=True,
        capture_output=True,
        env=r2_aws_env() if endpoint_url else None,
    )


def s3_object_exists(bucket: str, key: str, region: str) -> bool:
    return object_store_head_object(bucket, key, region)
