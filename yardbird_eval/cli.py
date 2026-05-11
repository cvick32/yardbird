from __future__ import annotations

import argparse

from .aws_backend import download_aws_artifacts, launch_aws_run, refresh_aws_run
from .common import (
    BENCHMARK_ROOT,
    DEFAULT_CONFIG,
    build_report_for_run,
    ensure_dir,
    load_manifest,
    print_run_summary,
    resolve_run_id,
)
from .lab_backend import (
    DEFAULT_LAB_R2_PREFIX,
    DEFAULT_LAB_R2_REGION,
    DEFAULT_LAB_WORKER_USER,
    download_lab_artifacts,
    env_default,
    launch_lab_run,
    refresh_lab_run,
)
from .local_backend import launch_local_run


def refresh_existing_run(manifest: dict, args: argparse.Namespace) -> dict:
    if manifest["env"] == "aws":
        return refresh_aws_run(manifest)
    if manifest["env"] == "local":
        return manifest
    if manifest["env"] == "lab":
        return refresh_lab_run(manifest, args)
    raise RuntimeError(
        f"Run {manifest['run_id']} uses unsupported environment {manifest['env']}"
    )


def maybe_generate_report(manifest: dict) -> None:
    if manifest["status"] != "COMPLETED":
        raise RuntimeError(
            f"Run {manifest['run_id']} is not complete yet; current status is {manifest['status']}"
        )

    if manifest["env"] == "aws":
        download_aws_artifacts(manifest)
    elif manifest["env"] == "lab":
        download_lab_artifacts(manifest)

    build_report_for_run(manifest)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Unified Yardbird benchmark launcher, tracker, and report generator"
    )
    parser.add_argument(
        "--env", choices=["local", "aws", "lab"], help="Execution environment"
    )
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
    parser.add_argument("--run-id", help="Existing run id to refresh or report on")
    parser.add_argument("--aws-run-id", help=argparse.SUPPRESS)
    parser.add_argument(
        "--status",
        action="store_true",
        help="Refresh and print status for an existing run",
    )
    parser.add_argument(
        "--generate-report",
        action="store_true",
        help="For an existing completed run, download artifacts if needed and build the report",
    )
    parser.add_argument(
        "--lab-proxmox-api-url",
        default=env_default("PROXMOX_API_URL"),
        help="Proxmox API root, for example https://proxmox.example:8006/api2/json",
    )
    parser.add_argument(
        "--lab-proxmox-token-id",
        default=env_default("PROXMOX_TOKEN_ID"),
        help="Proxmox API token id",
    )
    parser.add_argument(
        "--lab-proxmox-token-secret",
        default=env_default("PROXMOX_TOKEN_SECRET"),
        help="Proxmox API token secret",
    )
    parser.add_argument(
        "--lab-proxmox-node",
        default=env_default("PROXMOX_NODE"),
        help="Proxmox node to use for worker VMs",
    )
    parser.add_argument(
        "--lab-proxmox-insecure",
        action="store_true",
        help="Skip TLS verification for Proxmox API requests",
    )
    parser.add_argument(
        "--lab-worker-template",
        default=env_default("LAB_WORKER_TEMPLATE"),
        help="Proxmox VM template id to clone for lab workers",
    )
    parser.add_argument(
        "--lab-worker-user",
        default=env_default("LAB_WORKER_USER", DEFAULT_LAB_WORKER_USER),
        help="Cloud-init user to use when connecting to lab workers",
    )
    parser.add_argument(
        "--lab-worker-ssh-key",
        default=env_default("LAB_WORKER_SSH_KEY"),
        help="Private SSH key used to connect to lab workers",
    )
    parser.add_argument(
        "--lab-worker-ssh-public-key",
        default=env_default("LAB_WORKER_SSH_PUBLIC_KEY"),
        help="Optional public SSH key contents or file path for cloud-init",
    )
    parser.add_argument(
        "--lab-r2-bucket",
        default=env_default("LAB_R2_BUCKET"),
        help="R2 bucket for lab artifacts",
    )
    parser.add_argument(
        "--lab-r2-endpoint-url",
        default=env_default("LAB_R2_ENDPOINT_URL"),
        help="R2 S3-compatible endpoint URL",
    )
    parser.add_argument(
        "--lab-r2-region",
        default=env_default("LAB_R2_REGION", DEFAULT_LAB_R2_REGION),
        help="Region string to pass to the AWS CLI for R2 access",
    )
    parser.add_argument(
        "--lab-r2-prefix",
        default=env_default("LAB_R2_PREFIX", DEFAULT_LAB_R2_PREFIX),
        help="Object prefix for lab artifacts",
    )
    parser.add_argument(
        "--lab-keep-vms",
        action="store_true",
        help="Preserve worker VMs after they finish instead of auto-destroying them",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    ensure_dir(BENCHMARK_ROOT)

    existing_run_id = resolve_run_id(args)
    if existing_run_id:
        manifest = load_manifest(existing_run_id)
        manifest = refresh_existing_run(manifest, args)
        if args.generate_report:
            maybe_generate_report(manifest)

        print_run_summary(manifest)
        return 0

    if not args.env:
        raise RuntimeError("Provide either --env with benchmark types or --run-id")
    if not args.benchmark_type:
        raise RuntimeError("Provide at least one --benchmark-type")

    if args.env == "local":
        manifest = launch_local_run(args)
    elif args.env == "aws":
        manifest = launch_aws_run(args)
    else:
        manifest = launch_lab_run(args)

    print_run_summary(manifest)
    return 0
