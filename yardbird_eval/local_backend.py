from __future__ import annotations

from pathlib import Path
from typing import Any

from .common import (
    GARDEN_BIN,
    ROOT,
    STATUS_COMPLETED,
    STATUS_FAILED,
    STATUS_RUNNING,
    base_manifest,
    build_report_for_run,
    ensure_garden_binary,
    ensure_dir,
    iso_now,
    now_local,
    refresh_progress,
    run_command,
    run_id_for,
    save_manifest,
    timestamp_filename,
)


def launch_local_run(args: Any) -> dict[str, Any]:
    run_id = run_id_for("local", args.name)
    manifest = base_manifest(
        run_id, "local", args.benchmark_type, Path(args.config), args.name
    )
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
            command = [
                str(GARDEN_BIN),
                "--config",
                args.config,
                "--matrix",
                matrix,
                "--output",
                str(raw_path),
            ]
            if args.ranker_model:
                command.extend(["--ranker-model", args.ranker_model])
            if args.profile_costs:
                command.append("--profile-costs")

            run_command(
                command,
                cwd=ROOT,
                check=True,
                capture_output=False,
            )
            subrun["status"] = STATUS_COMPLETED
            subrun["completed_at"] = iso_now()
            subrun["duration_seconds"] = round(
                (now_local() - started).total_seconds(), 2
            )
        except Exception as exc:
            subrun["status"] = STATUS_FAILED
            subrun["completed_at"] = iso_now()
            subrun["duration_seconds"] = round(
                (now_local() - started).total_seconds(), 2
            )
            subrun["error"] = str(exc)
            refresh_progress(manifest)
            save_manifest(manifest)
            raise

        refresh_progress(manifest)
        save_manifest(manifest)

    build_report_for_run(manifest)
    return manifest
