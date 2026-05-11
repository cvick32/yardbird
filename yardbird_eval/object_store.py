from __future__ import annotations

from pathlib import Path

from .common import ensure_dir, run_command


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
    result = run_command(command, check=False)
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
    run_command(command, check=True, capture_output=True)


def s3_object_exists(bucket: str, key: str, region: str) -> bool:
    return object_store_head_object(bucket, key, region)
