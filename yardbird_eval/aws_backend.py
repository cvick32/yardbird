from __future__ import annotations

import json
import os
import shlex
import re
import tarfile
from pathlib import Path
from typing import Any

from .benchmark_selection import garden_filter_args
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


def extract_capture_archive(archive_path: Path, capture_root: Path) -> None:
    """Extract a worker capture archive without allowing links or path escapes."""
    capture_root.mkdir(parents=True, exist_ok=True)
    resolved_root = capture_root.resolve()
    with tarfile.open(archive_path, "r:gz") as archive:
        members = archive.getmembers()
        for member in members:
            if member.issym() or member.islnk():
                raise RuntimeError(
                    f"Capture archive contains unsupported link: {member.name}"
                )
            destination = (resolved_root / member.name).resolve()
            if destination != resolved_root and resolved_root not in destination.parents:
                raise RuntimeError(
                    f"Capture archive path escapes destination: {member.name}"
                )
        archive.extractall(resolved_root, members=members)


def terraform_outputs(account: str = "personal") -> dict[str, str]:
    workspace = "default" if account == "personal" else account
    environment = os.environ.copy()
    environment["TF_WORKSPACE"] = workspace
    result = run_command(
        ["terraform", "output", "-json"], cwd=TERRAFORM_DIR, env=environment
    )
    parsed = json.loads(result.stdout)
    return {key: value["value"] for key, value in parsed.items()}


def read_user_data(
    matrix: str,
    unique_name: str,
    s3_bucket: str,
    *,
    benchmark_config_path: str = "garden/benchmark_config.yaml",
    capture_solver_journals: bool = False,
    garden_args: list[str] | None = None,
    api_key_parameters: dict[str, str] | None = None,
    region: str = DEFAULT_AWS_REGION,
    git_ref: str | None = None,
) -> str:
    secret_lines = []
    for variable, parameter in (api_key_parameters or {}).items():
        if variable not in {"OPENAI_API_KEY", "JEV_API_KEY", "ANTHROPIC_API_KEY"}:
            raise ValueError(f"Unsupported API credential environment: {variable}")
        if not re.fullmatch(r"[A-Za-z0-9_./:-]+", parameter):
            raise ValueError("Expected an SSM parameter name or ARN")
        # These are references only. Never read controller API keys.
        secret_lines.extend([
            f'{variable}=$(aws ssm get-parameter --name {shlex.quote(parameter)} '
            f'--with-decryption --query Parameter.Value --output text --region {shlex.quote(region)})',
            f'test -n "${{{variable}}}"',
            f'export {variable}',
        ])
    template = USER_DATA_TEMPLATE.read_text()
    template = template.replace("${aws_region}", shlex.quote(region))
    template = template.replace("${api_key_setup}", "\n".join(secret_lines))
    checkout = ""
    if git_ref:
        if not re.fullmatch(r"[A-Za-z0-9_./-]+", git_ref):
            raise ValueError("Invalid git ref")
        checkout = f"git fetch origin {shlex.quote(git_ref)}\ngit checkout --detach FETCH_HEAD"
    template = template.replace("${pinned_checkout}", checkout)
    template = template.replace("${matrix_name}", matrix)
    template = template.replace("${unique_benchmark_name}", unique_name)
    template = template.replace("${s3_bucket_name}", s3_bucket)
    template = template.replace(
        "${repository_benchmark_config}", shlex.quote(benchmark_config_path)
    )
    template = template.replace(
        "${capture_solver_journals}",
        "true" if capture_solver_journals else "false",
    )
    template = template.replace(
        "${garden_args}", shlex.join(garden_args or [])
    )
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
    config_path = Path(args.config).expanduser().resolve()
    if not config_path.is_file():
        raise FileNotFoundError(f"AWS benchmark config not found: {config_path}")
    try:
        repository_config_path = config_path.relative_to(ROOT)
    except ValueError as error:
        raise ValueError(
            "AWS benchmark config must be checked into the Yardbird repository"
        ) from error

    run_id = run_id_for("aws", args.name)
    manifest = base_manifest(
        run_id, "aws", args.benchmark_type, config_path, args.name
    )
    run_dir = Path(manifest["run_dir"])
    aws_dir = ensure_dir(run_dir / "aws")
    account = args.aws_account
    outputs = terraform_outputs(account)
    region = outputs.get("aws_region", DEFAULT_AWS_REGION)
    launch_template_id = outputs["launch_template_id"]
    bucket = outputs["s3_bucket_name"]
    capture_solver_journals = bool(args.capture_solver_journals)
    manifest["capture_solver_journals"] = capture_solver_journals
    manifest["aws_account"] = account
    manifest["git_ref"] = getattr(args, "git_ref", None) or "main"
    manifest["benchmark_selection"] = args.benchmark_selection
    garden_args = garden_filter_args(args)
    if getattr(args, "profile", False):
        garden_args.append("--profile")

    for idx, matrix in enumerate(args.benchmark_type, start=1):
        remote_run_name = f"{matrix}-{now_local().strftime('%Y%m%d_%H%M%S')}-{idx:02d}"
        user_data = read_user_data(
            matrix,
            remote_run_name,
            bucket,
            benchmark_config_path=repository_config_path.as_posix(),
            capture_solver_journals=capture_solver_journals,
            garden_args=garden_args,
            api_key_parameters={
                env: parameter for env, parameter in {
                    "OPENAI_API_KEY": getattr(args, "openai_api_key_parameter", None),
                    "JEV_API_KEY": getattr(args, "jev_api_key_parameter", None),
                }.items() if parameter
            },
            region=region,
            git_ref=getattr(args, "git_ref", None),
        )
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
        subrun = {
            "benchmark_type": matrix,
            "status": STATUS_RUNNING,
            "started_at": iso_now(),
            "completed_at": None,
            "mode": "aws",
            "requires_completion_marker": True,
            "region": region,
            "instance_id": instance_id,
            "bucket": bucket,
            "remote_run_name": remote_run_name,
            "s3_prefix": f"benchmarks/{remote_run_name}",
            "result_path": str(run_dir / "raw" / matrix / timestamp_filename()),
            "download_dir": str(run_dir / "downloads" / matrix),
            "capture_solver_journals": capture_solver_journals,
        }
        if capture_solver_journals:
            subrun.update(
                {
                    "capture_archive_key": f"benchmarks/{remote_run_name}/captures.tar.gz",
                    "capture_root": str(run_dir / "captures" / matrix),
                }
            )
        manifest["subruns"].append(subrun)
        refresh_progress(manifest)
        save_manifest(manifest)

    return manifest


def refresh_aws_run(manifest: dict[str, Any]) -> dict[str, Any]:
    for subrun in manifest["subruns"]:
        # Remote artifacts and instances may expire after a successful download.
        if subrun["status"] == STATUS_COMPLETED or subrun.get("downloaded_at"):
            subrun["status"] = STATUS_COMPLETED
            if subrun.get("completed_at") is None:
                subrun["completed_at"] = subrun.get("downloaded_at") or iso_now()
            continue

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
        if completion_exists or (results_exist and not subrun.get("requires_completion_marker", False)):
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

        capture_archive_key = subrun.get("capture_archive_key")
        capture_archive_path = download_dir / "captures.tar.gz"
        if capture_archive_key:
            downloads["captures.tar.gz"] = capture_archive_path

        for remote_name, local_path in downloads.items():
            if local_path.exists() and remote_name != "results.json":
                continue
            remote_key = (
                str(capture_archive_key)
                if remote_name == "captures.tar.gz"
                else f"{prefix}/{remote_name}"
            )
            object_store_download(bucket, remote_key, local_path, region)

        if capture_archive_key:
            capture_root = Path(
                subrun.get("capture_root")
                or Path(manifest["run_dir"])
                / "captures"
                / subrun["benchmark_type"]
            )
            extraction_marker = capture_root / ".extracted"
            if not extraction_marker.exists():
                extract_capture_archive(capture_archive_path, capture_root)
                extraction_marker.write_text("complete\n")
            subrun["capture_root"] = str(capture_root)
            subrun["capture_archive_path"] = str(capture_archive_path)

        api_root = raw_path.with_suffix(".api")
        run_command(["aws", "s3", "sync", f"s3://{bucket}/{prefix}/api/",
                     str(api_root), "--region", region, "--only-show-errors"])
        subrun["downloaded_at"] = iso_now()
        subrun["download_dir"] = str(download_dir)
        subrun["result_path"] = str(raw_path)

    save_manifest(manifest)


def sync_partial_aws_artifacts(manifest: dict[str, Any]) -> None:
    """Download a running snapshot without declaring the subrun complete."""
    for subrun in manifest["subruns"]:
        bucket, prefix, region = (subrun[k] for k in ("bucket", "s3_prefix", "region"))
        raw_path = Path(subrun["result_path"])
        key = f"{prefix}/results.json"
        if not s3_object_exists(bucket, key, region):
            key = f"{prefix}/partial.json"
        if not s3_object_exists(bucket, key, region):
            continue
        ensure_dir(raw_path.parent)
        temporary = raw_path.with_suffix(".download")
        object_store_download(bucket, key, temporary, region)
        # Validate before replacing the last usable snapshot.
        json.loads(temporary.read_text())
        temporary.replace(raw_path)
        run_command(["aws", "s3", "sync", f"s3://{bucket}/{prefix}/api/",
                     str(raw_path.with_suffix(".api")), "--region", region,
                     "--only-show-errors"])
        subrun["partial_synced_at"] = iso_now()
    save_manifest(manifest)
