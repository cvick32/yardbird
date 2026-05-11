from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .common import (
    ROOT,
    STATUS_COMPLETED,
    STATUS_FAILED,
    STATUS_RUNNING,
    base_manifest,
    ensure_dir,
    iso_now,
    now_local,
    refresh_progress,
    run_command,
    run_id_for,
    save_manifest,
    slugify,
    timestamp_filename,
)
from .object_store import object_store_download, s3_object_exists


TERRAFORM_DIR = ROOT / "terraform"
USER_DATA_TEMPLATE = TERRAFORM_DIR / "user_data.sh"
DEFAULT_AWS_REGION = "us-east-2"


def terraform_outputs() -> dict[str, str]:
    result = run_command(["terraform", "output", "-json"], cwd=TERRAFORM_DIR)
    parsed = json.loads(result.stdout)
    return {key: value["value"] for key, value in parsed.items()}


def read_user_data(matrix: str, unique_name: str, s3_bucket: str) -> str:
    template = USER_DATA_TEMPLATE.read_text()
    template = template.replace("${matrix_name}", matrix)
    template = template.replace("${unique_benchmark_name}", unique_name)
    template = template.replace("${s3_bucket_name}", s3_bucket)
    return template


def aws_cli_json(args: list[str]) -> dict[str, Any]:
    result = run_command(["aws", *args, "--output", "json"])
    return json.loads(result.stdout)


def describe_instance_state(instance_id: str, region: str) -> str | None:
    result = run_command(
        [
            "aws",
            "ec2",
            "describe-instances",
            "--instance-ids",
            instance_id,
            "--region",
            region,
            "--output",
            "json",
        ],
        check=False,
    )
    if result.returncode != 0:
        return None

    payload = json.loads(result.stdout)
    reservations = payload.get("Reservations", [])
    if not reservations:
        return None
    instances = reservations[0].get("Instances", [])
    if not instances:
        return None
    return instances[0].get("State", {}).get("Name")


def launch_aws_run(args) -> dict[str, Any]:
    run_id = run_id_for("aws", args.name)
    manifest = base_manifest(
        run_id, "aws", args.benchmark_type, Path(args.config), args.name
    )
    run_dir = Path(manifest["run_dir"])
    aws_dir = ensure_dir(run_dir / "aws")
    outputs = terraform_outputs()
    region = outputs.get("aws_region", DEFAULT_AWS_REGION)
    launch_template_id = outputs["launch_template_id"]
    bucket = outputs["s3_bucket_name"]

    for idx, matrix in enumerate(args.benchmark_type, start=1):
        remote_run_name = f"{matrix}-{now_local().strftime('%Y%m%d_%H%M%S')}-{idx:02d}"
        user_data = read_user_data(matrix, remote_run_name, bucket)
        user_data_path = aws_dir / f"{slugify(matrix)}_user_data.sh"
        user_data_path.write_text(user_data)

        tag_specifications = [
            {
                "ResourceType": "instance",
                "Tags": [
                    {"Key": "BenchmarkRun", "Value": f"{matrix}_{remote_run_name}"},
                    {"Key": "Timestamp", "Value": remote_run_name},
                ],
            }
        ]

        response = aws_cli_json(
            [
                "ec2",
                "run-instances",
                "--launch-template",
                f"LaunchTemplateId={launch_template_id}",
                "--user-data",
                f"fileb://{user_data_path}",
                "--tag-specifications",
                json.dumps(tag_specifications),
                "--region",
                region,
            ]
        )
        instance_id = response["Instances"][0]["InstanceId"]
        manifest["subruns"].append(
            {
                "benchmark_type": matrix,
                "status": STATUS_RUNNING,
                "started_at": iso_now(),
                "completed_at": None,
                "mode": "aws",
                "region": region,
                "instance_id": instance_id,
                "bucket": bucket,
                "remote_run_name": remote_run_name,
                "s3_prefix": f"benchmarks/{remote_run_name}",
                "result_path": str(run_dir / "raw" / matrix / timestamp_filename()),
                "download_dir": str(run_dir / "downloads" / matrix),
            }
        )
        refresh_progress(manifest)
        save_manifest(manifest)

    return manifest


def refresh_aws_run(manifest: dict[str, Any]) -> dict[str, Any]:
    for subrun in manifest["subruns"]:
        bucket = subrun["bucket"]
        region = subrun["region"]
        prefix = subrun["s3_prefix"]
        instance_id = subrun["instance_id"]

        results_key = f"{prefix}/results.json"
        completion_key = f"{prefix}/completion.txt"
        results_exist = s3_object_exists(bucket, results_key, region)
        completion_exists = s3_object_exists(bucket, completion_key, region)
        state = describe_instance_state(instance_id, region)
        subrun["last_observed_instance_state"] = state
        subrun["last_checked_at"] = iso_now()

        new_status = subrun["status"]
        if results_exist or completion_exists:
            new_status = STATUS_COMPLETED
        elif state in {"terminated", "stopped", "stopping"}:
            new_status = STATUS_FAILED
        else:
            new_status = STATUS_RUNNING

        if subrun["status"] != new_status:
            subrun["status"] = new_status
            if new_status in {STATUS_COMPLETED, STATUS_FAILED}:
                subrun["completed_at"] = iso_now()

    refresh_progress(manifest)
    save_manifest(manifest)
    return manifest


def download_aws_artifacts(manifest: dict[str, Any]) -> None:
    for subrun in manifest["subruns"]:
        if subrun["status"] != STATUS_COMPLETED:
            raise RuntimeError(
                f"Cannot download artifacts for incomplete benchmark type {subrun['benchmark_type']}"
            )

        raw_path = Path(subrun["result_path"])
        download_dir = ensure_dir(Path(subrun["download_dir"]))
        bucket = subrun["bucket"]
        region = subrun["region"]
        prefix = subrun["s3_prefix"]

        downloads = {
            "results.json": raw_path,
            "status.log": download_dir / "status.log",
            "user-data.log": download_dir / "user-data.log",
            "completion.txt": download_dir / "completion.txt",
        }

        for remote_name, local_path in downloads.items():
            if local_path.exists():
                continue
            object_store_download(bucket, f"{prefix}/{remote_name}", local_path, region)

        subrun["downloaded_at"] = iso_now()
        subrun["download_dir"] = str(download_dir)
        subrun["result_path"] = str(raw_path)

    save_manifest(manifest)
