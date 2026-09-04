from __future__ import annotations

import argparse
import os
import sys

from .aws_backend import download_aws_artifacts, launch_aws_run, refresh_aws_run
from .benchmark_selection import (
    select_difficult_benchmarks,
    select_formula_research_cohort,
)
from .common import (
    BENCHMARK_ROOT,
    DEFAULT_CONFIG,
    build_report_for_run,
    ensure_dir,
    load_manifest,
    load_dotenv,
    prefer_aws_dotenv,
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
    teardown_lab_subrun,
)
from .instrumentation_backend import (
    compare_downloaded_aws_run,
    launch_instrumentation_run,
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


def maybe_teardown_subrun(manifest: dict, args: argparse.Namespace) -> dict:
    if manifest["env"] != "lab":
        raise RuntimeError(
            f"Run {manifest['run_id']} uses unsupported environment {manifest['env']} for teardown"
        )
    return teardown_lab_subrun(manifest, args, args.teardown_subrun_index)


def legacy_parser() -> argparse.ArgumentParser:
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
    parser.add_argument(
        "--ranker-model",
        help="Path to a logistic-regression model JSON to pass through to garden/Yardbird",
    )
    parser.add_argument(
        "--profile",
        action="store_true",
        help="Include Yardbird profiling data in benchmark JSON",
    )
    parser.add_argument(
        "--synthesis-trigger",
        choices=[
            "off",
            "detect",
            "non-local",
            "manual-after-n",
            "refinement-limit",
            "repeated-pattern",
        ],
        default="off",
        help="Auxiliary-variable synthesis trigger (default: off)",
    )
    parser.add_argument(
        "--synthesis-guard-policy",
        choices=["true", "axiom-local", "interpolant", "llm"],
        default="true",
        help="Guard policy for synthesized auxiliary variables (default: true)",
    )
    parser.add_argument(
        "--synthesis-after",
        type=int,
        help="Refinement step for the manual-after-n synthesis trigger",
    )
    parser.add_argument(
        "--synthesis-refinement-limit-window",
        type=int,
        help="Remaining-refinement window for the refinement-limit trigger",
    )
    parser.add_argument(
        "--synthesis-repeated-pattern-threshold",
        type=int,
        help="Conflict repetition count for the repeated-pattern trigger",
    )
    parser.add_argument(
        "--difficult-benchmarks",
        nargs="?",
        const="auto",
        metavar="BASELINE",
        help=(
            "Only run benchmarks where abstract BMC-cost or concrete timed out or "
            "exceeded the difficult threshold in BASELINE. BASELINE may be a "
            "main_eval run id, run directory, manifest, or Garden result JSON. "
            "Omit BASELINE to use the newest downloaded run containing both baselines."
        ),
    )
    parser.add_argument(
        "--difficult-threshold-seconds",
        type=float,
        default=30.0,
        help="Runtime cutoff for --difficult-benchmarks (default: 30 seconds)",
    )
    parser.add_argument(
        "--formula-research-cohort",
        nargs="?",
        const="auto",
        metavar="BASELINE",
        help=(
            "Run the fixed formula-transformation guardrails plus benchmarks where "
            "concrete succeeds and abstract BMC-cost times out in BASELINE. BASELINE "
            "accepts the same sources as --difficult-benchmarks."
        ),
    )
    parser.add_argument(
        "--limit",
        type=int,
        help="Maximum benchmarks to run after difficult-benchmark filtering",
    )
    parser.add_argument(
        "--sample-seed",
        type=int,
        help="Deterministic Garden sampling seed when --limit is set",
    )
    parser.add_argument(
        "--capture-solver-journals",
        action="store_true",
        help=(
            "AWS only: preserve incremental SMT2 solver journals for later local replay. "
            "Disabled by default because capture I/O changes benchmark runtime."
        ),
    )
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
        "--teardown-subrun-index",
        type=int,
        help="For an existing lab run, destroy one completed or failed worker VM by subrun index",
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
    return parser


def add_z3_replay_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--z3-build-dir",
        help="Reuse an existing z3-builder output instead of building inside the run",
    )
    parser.add_argument(
        "--z3-checkout",
        help="Z3 checkout used to build the pinned stock and instrumented pair",
    )
    parser.add_argument(
        "--instrumented-z3-checkout",
        help="Optional separate instrumented Z3 checkout",
    )
    parser.add_argument(
        "--z3-build-jobs",
        type=int,
        default=os.cpu_count() or 1,
        help="Parallel jobs for z3-builder",
    )
    parser.add_argument("--warmups", type=int, default=3)
    parser.add_argument("--repetitions", type=int, default=15)
    parser.add_argument("--replay-timeout", type=float, default=60.0)


def instrumentation_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run Garden benchmarks and compare captured solver sessions with instrumented Z3"
    )
    parser.add_argument(
        "--config",
        default=str(DEFAULT_CONFIG),
        help="Path to the Garden benchmark config YAML",
    )
    parser.add_argument(
        "--run-type",
        action="append",
        required=True,
        help="Garden matrix name to run. Can be repeated.",
    )
    parser.add_argument("--run-id", required=True, help="New evaluation run id")
    parser.add_argument("--name", help="Optional friendly name for the run")
    parser.add_argument(
        "--ranker-model",
        help="Logistic-regression model JSON to pass through to Garden/Yardbird",
    )
    add_z3_replay_arguments(parser)
    return parser


def downloaded_instrumentation_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Compare solver captures downloaded from a completed AWS run"
    )
    parser.add_argument("--run-id", required=True, help="Completed AWS evaluation run id")
    parser.add_argument(
        "--resume",
        action="store_true",
        help="Reuse compatible per-capture comparison reports that already exist",
    )
    add_z3_replay_arguments(parser)
    return parser


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    values = list(sys.argv[1:] if argv is None else argv)
    if values and values[0] in {
        "compare_with_instrumentation",
        "compare-with-instrumentation",
    }:
        args = instrumentation_parser().parse_args(values[1:])
        args.command = "compare_with_instrumentation"
        return args
    if values and values[0] in {
        "compare_downloaded_instrumentation",
        "compare-downloaded-instrumentation",
    }:
        args = downloaded_instrumentation_parser().parse_args(values[1:])
        args.command = "compare_downloaded_instrumentation"
        return args
    if values and values[0] in {"generate-report", "generate_report"}:
        report_parser = argparse.ArgumentParser(
            description="Generate the workbook and PDF for a completed evaluation run"
        )
        report_parser.add_argument("--run-id", required=True)
        report_args = report_parser.parse_args(values[1:])
        args = legacy_parser().parse_args(
            ["--run-id", report_args.run_id, "--generate-report"]
        )
        args.command = "generate-report"
        return args
    args = legacy_parser().parse_args(values)
    args.command = "legacy"
    return args


def main(argv: list[str] | None = None) -> int:
    load_dotenv()
    args = parse_args(argv)
    ensure_dir(BENCHMARK_ROOT)

    if args.command == "compare_with_instrumentation":
        manifest = launch_instrumentation_run(args)
        print_run_summary(manifest)
        return 0
    if args.command == "compare_downloaded_instrumentation":
        manifest = load_manifest(args.run_id)
        if manifest.get("env") == "aws":
            prefer_aws_dotenv()
        manifest = refresh_existing_run(manifest, args)
        if manifest["status"] != "COMPLETED":
            raise RuntimeError(
                f"Run {args.run_id} is not complete yet; current status is {manifest['status']}"
            )
        if manifest["env"] != "aws":
            raise RuntimeError(
                f"Run {args.run_id} is not an AWS run: {manifest['env']}"
            )
        download_aws_artifacts(manifest)
        manifest = compare_downloaded_aws_run(args, manifest)
        print_run_summary(manifest)
        return 0

    existing_run_id = resolve_run_id(args)
    if existing_run_id:
        manifest = load_manifest(existing_run_id)
        if manifest.get("env") == "aws":
            prefer_aws_dotenv()
        if args.teardown_subrun_index is not None:
            manifest = maybe_teardown_subrun(manifest, args)
        else:
            manifest = refresh_existing_run(manifest, args)
        if args.generate_report:
            maybe_generate_report(manifest)

        print_run_summary(manifest)
        return 0

    if not args.env:
        raise RuntimeError("Provide either --env with benchmark types or --run-id")
    if not args.benchmark_type:
        raise RuntimeError("Provide at least one --benchmark-type")
    if args.env != "local" and (args.ranker_model or args.profile):
        raise RuntimeError(
            "--ranker-model and --profile are currently supported for --env local only"
        )
    if args.capture_solver_journals and args.env != "aws":
        raise RuntimeError(
            "--capture-solver-journals is currently supported for --env aws only"
        )
    if args.limit is not None and args.limit <= 0:
        raise RuntimeError("--limit must be greater than zero")
    if args.difficult_benchmarks and args.formula_research_cohort:
        raise RuntimeError(
            "Use only one of --difficult-benchmarks and --formula-research-cohort"
        )
    if args.difficult_benchmarks:
        args.benchmark_selection = select_difficult_benchmarks(
            args.difficult_benchmarks,
            args.difficult_threshold_seconds,
        )
        args.benchmark_selection["limit"] = args.limit
        args.benchmark_selection["sample_seed"] = args.sample_seed
        print(
            "Difficult benchmark cohort: "
            f"{len(args.benchmark_selection['benchmarks'])} benchmarks from "
            f"{args.benchmark_selection['source']} "
            f"(>{args.difficult_threshold_seconds:g}s or timeout)"
        )
    elif args.formula_research_cohort:
        args.benchmark_selection = select_formula_research_cohort(
            args.formula_research_cohort
        )
        args.benchmark_selection["limit"] = args.limit
        args.benchmark_selection["sample_seed"] = args.sample_seed
        print(
            "Formula research cohort: "
            f"{len(args.benchmark_selection['benchmarks'])} benchmarks from "
            f"{args.benchmark_selection['source']}"
        )
    else:
        args.benchmark_selection = None
    if args.env == "aws":
        prefer_aws_dotenv()

    if args.env == "local":
        manifest = launch_local_run(args)
    elif args.env == "aws":
        manifest = launch_aws_run(args)
    else:
        manifest = launch_lab_run(args)

    print_run_summary(manifest)
    return 0
