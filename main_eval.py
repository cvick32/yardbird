#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent
BENCHMARK_ROOT = ROOT / "benchmark_results" / "main_eval"
INDEX_PATH = BENCHMARK_ROOT / "runs_index.json"
DEFAULT_CONFIG = ROOT / "garden" / "benchmark_config.yaml"
GARDEN_BIN = ROOT / "target" / "release" / "garden"
PAPER_GRAPHICS_VENV_PY = ROOT / "paper-graphics" / ".venv" / "bin" / "python"
REPORT_BUILDER = ROOT / "paper-graphics" / "report" / "build_report.py"
TERRAFORM_DIR = ROOT / "terraform"
USER_DATA_TEMPLATE = TERRAFORM_DIR / "user_data.sh"
DEFAULT_AWS_REGION = "us-east-2"
STATUS_RUNNING = "RUNNING"
STATUS_COMPLETED = "COMPLETED"
STATUS_FAILED = "FAILED"


class CommandError(RuntimeError):
    pass


def now_local() -> datetime:
    return datetime.now().astimezone()


def iso_now() -> str:
    return now_local().isoformat()


def ensure_dir(path: Path) -> Path:
    path.mkdir(parents=True, exist_ok=True)
    return path


def slugify(value: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9]+", "-", value.strip()).strip("-").lower()
    return slug or "run"


def timestamp_filename(dt: datetime | None = None) -> str:
    current = dt or now_local()
    return current.strftime("%m_%d_%Y_%H_%M.json")


def run_id_for(env: str, name: str | None = None) -> str:
    prefix = slugify(name) if name else "eval"
    return f"{prefix}-{env}-{now_local().strftime('%Y%m%d_%H%M%S')}"


def load_json(path: Path, default: Any = None) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text())


def write_json(path: Path, payload: Any) -> None:
    ensure_dir(path.parent)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def run_command(
    args: list[str],
    cwd: Path | None = None,
    check: bool = True,
    capture_output: bool = True,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        args,
        cwd=str(cwd) if cwd else None,
        text=True,
        capture_output=capture_output,
    )
    if check and result.returncode != 0:
        stderr = result.stderr.strip() if result.stderr else ""
        stdout = result.stdout.strip() if result.stdout else ""
        message = stderr or stdout or f"Command failed with exit code {result.returncode}"
        raise CommandError(f"{' '.join(args)}\n{message}")
    return result


def choose_report_python() -> str:
    if PAPER_GRAPHICS_VENV_PY.exists():
        return str(PAPER_GRAPHICS_VENV_PY)
    return shutil.which("python3") or sys.executable


def read_index() -> dict[str, Any]:
    return load_json(INDEX_PATH, default={"runs": []})


def update_index(manifest: dict[str, Any]) -> None:
    index = read_index()
    runs = [run for run in index.get("runs", []) if run.get("run_id") != manifest["run_id"]]
    runs.append(
        {
            "run_id": manifest["run_id"],
            "name": manifest.get("name"),
            "env": manifest["env"],
            "status": manifest["status"],
            "started_at": manifest["started_at"],
            "updated_at": manifest["updated_at"],
            "benchmark_types": manifest["benchmark_types"],
            "manifest_path": manifest["manifest_path"],
        }
    )
    runs.sort(key=lambda run: run["started_at"], reverse=True)
    index["runs"] = runs
    write_json(INDEX_PATH, index)


def manifest_path_for(run_id: str) -> Path:
    return BENCHMARK_ROOT / run_id / "run.json"


def save_manifest(manifest: dict[str, Any]) -> None:
    manifest["updated_at"] = iso_now()
    path = Path(manifest["manifest_path"])
    write_json(path, manifest)
    update_index(manifest)


def load_manifest(run_id: str) -> dict[str, Any]:
    path = manifest_path_for(run_id)
    if not path.exists():
        raise FileNotFoundError(f"Unknown run id: {run_id}")
    return load_json(path)


def summarize_status(subruns: list[dict[str, Any]]) -> tuple[str, dict[str, int]]:
    counts = {STATUS_RUNNING: 0, STATUS_COMPLETED: 0, STATUS_FAILED: 0}
    for subrun in subruns:
        counts[subrun["status"]] = counts.get(subrun["status"], 0) + 1

    if counts[STATUS_FAILED]:
        overall = STATUS_FAILED
    elif counts[STATUS_RUNNING]:
        overall = STATUS_RUNNING
    else:
        overall = STATUS_COMPLETED
    return overall, counts


def base_manifest(
    run_id: str,
    env: str,
    benchmark_types: list[str],
    config_path: Path,
    name: str | None,
) -> dict[str, Any]:
    run_dir = ensure_dir(BENCHMARK_ROOT / run_id)
    manifest = {
        "run_id": run_id,
        "name": name or run_id,
        "env": env,
        "status": STATUS_RUNNING,
        "started_at": iso_now(),
        "updated_at": iso_now(),
        "completed_at": None,
        "benchmark_types": benchmark_types,
        "config_path": str(config_path),
        "run_dir": str(run_dir),
        "manifest_path": str(run_dir / "run.json"),
        "progress": {
            "completed": 0,
            "failed": 0,
            "running": len(benchmark_types),
            "total": len(benchmark_types),
        },
        "report": None,
        "subruns": [],
    }
    return manifest


def refresh_progress(manifest: dict[str, Any]) -> None:
    overall, counts = summarize_status(manifest["subruns"])
    manifest["status"] = overall
    manifest["progress"] = {
        "completed": counts.get(STATUS_COMPLETED, 0),
        "failed": counts.get(STATUS_FAILED, 0),
        "running": counts.get(STATUS_RUNNING, 0),
        "total": len(manifest["subruns"]),
    }
    if overall == STATUS_COMPLETED and manifest.get("completed_at") is None:
        manifest["completed_at"] = iso_now()


def ensure_garden_binary() -> None:
    if GARDEN_BIN.exists():
        return
    run_command(["cargo", "build", "--release", "-p", "garden"], cwd=ROOT, check=True)


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


def aws_cli_success(args: list[str]) -> bool:
    result = run_command(["aws", *args], check=False)
    return result.returncode == 0


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


def s3_object_exists(bucket: str, key: str, region: str) -> bool:
    return aws_cli_success(
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


def relative_to_root(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def launch_local_run(args: argparse.Namespace) -> dict[str, Any]:
    ensure_dir(BENCHMARK_ROOT)
    run_id = run_id_for("local", args.name)
    manifest = base_manifest(run_id, "local", args.benchmark_type, Path(args.config), args.name)
    run_dir = Path(manifest["run_dir"])
    ensure_garden_binary()

    for matrix in args.benchmark_type:
        raw_dir = ensure_dir(run_dir / "raw" / matrix)
        raw_path = raw_dir / timestamp_filename()
        subrun = {
            "benchmark_type": matrix,
            "status": STATUS_RUNNING,
            "started_at": iso_now(),
            "completed_at": None,
            "result_path": str(raw_path),
            "duration_seconds": None,
            "mode": "local",
        }
        manifest["subruns"].append(subrun)
        save_manifest(manifest)

        started = now_local()
        try:
            run_command(
                [
                    str(GARDEN_BIN),
                    "--config",
                    args.config,
                    "--matrix",
                    matrix,
                    "--output",
                    str(raw_path),
                ],
                cwd=ROOT,
                check=True,
                capture_output=False,
            )
            subrun["status"] = STATUS_COMPLETED
            subrun["completed_at"] = iso_now()
            subrun["duration_seconds"] = round((now_local() - started).total_seconds(), 2)
        except Exception as exc:
            subrun["status"] = STATUS_FAILED
            subrun["completed_at"] = iso_now()
            subrun["duration_seconds"] = round((now_local() - started).total_seconds(), 2)
            subrun["error"] = str(exc)
            refresh_progress(manifest)
            save_manifest(manifest)
            raise

        refresh_progress(manifest)
        save_manifest(manifest)

    build_report_for_run(manifest)
    return manifest


def launch_aws_run(args: argparse.Namespace) -> dict[str, Any]:
    ensure_dir(BENCHMARK_ROOT)
    run_id = run_id_for("aws", args.name)
    manifest = base_manifest(run_id, "aws", args.benchmark_type, Path(args.config), args.name)
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
        launched_at = iso_now()
        manifest["subruns"].append(
            {
                "benchmark_type": matrix,
                "status": STATUS_RUNNING,
                "started_at": launched_at,
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
    changed = False
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
            changed = True
            subrun["status"] = new_status
            if new_status in {STATUS_COMPLETED, STATUS_FAILED}:
                subrun["completed_at"] = iso_now()

    refresh_progress(manifest)
    if changed:
        save_manifest(manifest)
    else:
        manifest["updated_at"] = iso_now()
        save_manifest(manifest)
    return manifest


def download_aws_artifacts(manifest: dict[str, Any]) -> None:
    run_dir = Path(manifest["run_dir"])
    for subrun in manifest["subruns"]:
        if subrun["status"] != STATUS_COMPLETED:
            raise RuntimeError(
                f"Cannot download artifacts for incomplete benchmark type {subrun['benchmark_type']}"
            )

        raw_path = Path(subrun["result_path"])
        ensure_dir(raw_path.parent)
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
            remote_uri = f"s3://{bucket}/{prefix}/{remote_name}"
            run_command(
                ["aws", "s3", "cp", remote_uri, str(local_path), "--region", region],
                check=True,
                capture_output=True,
            )

        subrun["downloaded_at"] = iso_now()
        subrun["download_dir"] = str(download_dir)
        subrun["result_path"] = str(raw_path)

    save_manifest(manifest)


def build_report_for_run(manifest: dict[str, Any]) -> None:
    if manifest["status"] != STATUS_COMPLETED:
        raise RuntimeError(
            f"Run {manifest['run_id']} is not complete yet; current status is {manifest['status']}"
        )

    run_dir = Path(manifest["run_dir"])
    report_dir = ensure_dir(run_dir / "report")
    report_python = choose_report_python()

    run_command(
        [
            report_python,
            str(REPORT_BUILDER),
            "--manifest",
            manifest["manifest_path"],
            "--run-dir",
            str(run_dir),
        ],
        cwd=ROOT,
        check=True,
        capture_output=False,
    )

    report_meta_path = report_dir / "report_metadata.json"
    if report_meta_path.exists():
        manifest["report"] = load_json(report_meta_path)
        save_manifest(manifest)


def print_run_summary(manifest: dict[str, Any]) -> None:
    print(f"Run ID: {manifest['run_id']}")
    print(f"Name: {manifest.get('name')}")
    print(f"Environment: {manifest['env']}")
    print(f"Status: {manifest['status']}")
    print(
        "Progress: "
        f"{manifest['progress']['completed']}/{manifest['progress']['total']} completed, "
        f"{manifest['progress']['running']} running, "
        f"{manifest['progress']['failed']} failed"
    )
    print(f"Started: {manifest['started_at']}")
    if manifest.get("completed_at"):
        print(f"Completed: {manifest['completed_at']}")
    print(f"Manifest: {relative_to_root(Path(manifest['manifest_path']))}")

    for subrun in manifest["subruns"]:
        line = (
            f"  - {subrun['benchmark_type']}: {subrun['status']}"
            f" ({subrun['mode']})"
        )
        if subrun["mode"] == "aws":
            line += f" instance={subrun['instance_id']}"
        print(line)

    if manifest.get("report"):
        report = manifest["report"]
        workbook = report.get("workbook_pdf")
        if workbook:
            print(f"Workbook PDF: {workbook}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Unified Yardbird benchmark launcher, tracker, and report generator"
    )
    parser.add_argument("--env", choices=["local", "aws"], help="Execution environment")
    parser.add_argument(
        "--benchmark-type",
        action="append",
        default=[],
        help="Garden matrix name to run. Can be repeated.",
    )
    parser.add_argument(
        "--config",
        default=str(DEFAULT_CONFIG),
        help="Path to the garden benchmark config YAML",
    )
    parser.add_argument("--name", help="Optional friendly name for the evaluation run")
    parser.add_argument(
        "--aws-run-id",
        help="Existing AWS-backed run id to refresh or report on",
    )
    parser.add_argument(
        "--status",
        action="store_true",
        help="Refresh and print status for an existing AWS run",
    )
    parser.add_argument(
        "--generate-report",
        action="store_true",
        help="For an existing completed run, download artifacts if needed and build the report",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    ensure_dir(BENCHMARK_ROOT)

    if args.aws_run_id:
        manifest = load_manifest(args.aws_run_id)
        if manifest["env"] != "aws":
            raise RuntimeError(f"Run {args.aws_run_id} is not an AWS run")

        manifest = refresh_aws_run(manifest)
        if args.generate_report:
            if manifest["status"] != STATUS_COMPLETED:
                raise RuntimeError(
                    f"Run {manifest['run_id']} is not complete yet; current status is {manifest['status']}"
                )
            download_aws_artifacts(manifest)
            build_report_for_run(manifest)

        print_run_summary(manifest)
        return 0

    if not args.env:
        raise RuntimeError("Provide either --env with benchmark types or --aws-run-id")
    if not args.benchmark_type:
        raise RuntimeError("Provide at least one --benchmark-type")

    if args.env == "local":
        manifest = launch_local_run(args)
    else:
        manifest = launch_aws_run(args)

    print_run_summary(manifest)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
