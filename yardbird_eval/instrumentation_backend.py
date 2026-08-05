from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Callable

from tools.z3_profile import (
    ComparisonReport,
    compare_capture,
    load_builder_manifest,
    write_comparison_report,
)

from .common import (
    BENCHMARK_ROOT,
    GARDEN_BIN,
    ROOT,
    STATUS_COMPLETED,
    STATUS_FAILED,
    STATUS_RUNNING,
    base_manifest,
    ensure_dir,
    ensure_garden_binary,
    iso_now,
    load_json,
    now_local,
    refresh_progress,
    run_command,
    save_manifest,
    timestamp_filename,
    write_json,
)


SOLVED_RESULT_TYPES = {"Success", "_FoundProof"}


def validate_new_run_id(run_id: str) -> None:
    allowed = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._-"
    if not run_id or any(character not in allowed for character in run_id):
        raise RuntimeError(
            "--run-id may contain only letters, numbers, periods, underscores, and hyphens"
        )
    if run_id in {".", ".."}:
        raise RuntimeError("--run-id must name a run directory")
    if (BENCHMARK_ROOT / run_id).exists():
        raise RuntimeError(f"Run already exists: {run_id}")


def discover_z3_checkout(explicit: str | None = None) -> Path:
    def is_checkout(path: Path) -> bool:
        return (path / "scripts" / "VERSION.txt").is_file() and (path / ".git").exists()

    if explicit:
        resolved = Path(explicit).expanduser().resolve()
        if not is_checkout(resolved):
            raise RuntimeError(f"--z3-checkout is not a Z3 checkout: {resolved}")
        return resolved

    candidates: list[Path] = []
    if os.environ.get("YARDBIRD_Z3_CHECKOUT"):
        candidates.append(Path(os.environ["YARDBIRD_Z3_CHECKOUT"]))

    candidates.append(ROOT.parent / "z3")
    common_dir = run_command(
        ["git", "rev-parse", "--path-format=absolute", "--git-common-dir"],
        cwd=ROOT,
    ).stdout.strip()
    if common_dir:
        candidates.append(Path(common_dir).resolve().parent.parent / "z3")

    seen: set[Path] = set()
    for candidate in candidates:
        resolved = candidate.expanduser().resolve()
        if resolved in seen:
            continue
        seen.add(resolved)
        if is_checkout(resolved):
            return resolved

    searched = ", ".join(str(path.expanduser()) for path in candidates)
    raise RuntimeError(
        "Could not find the instrumented Z3 checkout. Pass --z3-checkout or set "
        f"YARDBIRD_Z3_CHECKOUT. Searched: {searched}"
    )


def prepare_z3_build(args: Any, run_dir: Path) -> tuple[Path, dict[str, Any]]:
    if args.z3_build_dir:
        build_dir = Path(args.z3_build_dir).expanduser().resolve()
        builder_manifest = load_builder_manifest(build_dir)
    else:
        checkout = discover_z3_checkout(args.z3_checkout)
        instrumented_checkout = (
            Path(args.instrumented_z3_checkout).expanduser().resolve()
            if args.instrumented_z3_checkout
            else checkout
        )
        build_dir = run_dir / "z3-build"
        command = [
            sys.executable,
            str(ROOT / "tools" / "z3-builder" / "z3_builder.py"),
            "--z3-checkout",
            str(checkout),
            "--instrumented-checkout",
            str(instrumented_checkout),
            "--output",
            str(build_dir),
            "--jobs",
            str(args.z3_build_jobs),
        ]
        completed = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            check=False,
        )
        if completed.returncode != 0:
            detail = completed.stdout.strip()
            suffix = f"\n{detail}" if detail else ""
            raise RuntimeError(
                f"z3-builder failed with exit code {completed.returncode}{suffix}"
            )
        builder_manifest = load_builder_manifest(build_dir)

    snapshot_path = run_dir / "instrumentation" / "z3-builder-manifest.json"
    write_json(snapshot_path, builder_manifest)
    return build_dir, builder_manifest


def _result_type(result: Any) -> str:
    if isinstance(result, dict) and result:
        return str(next(iter(result)))
    return "Unknown"


def _clean_example_name(value: str) -> str:
    if "_examples/" in value:
        return "examples/" + value.split("_examples/", 1)[1]
    return value


def _resolve_capture_dir(
    capture_value: Any, downloaded_capture_root: Path | None
) -> Path | None:
    if not capture_value:
        return None
    capture_path = Path(str(capture_value))
    if downloaded_capture_root is None:
        return capture_path.expanduser().resolve()

    # Garden assigns captures as <root>/<matrix-index>/<benchmark-index>. The
    # worker root may be relative or absolute, so only those stable final path
    # components are portable across machines.
    if len(capture_path.parts) < 2:
        raise RuntimeError(f"Invalid Garden capture path: {capture_path}")
    resolved_root = downloaded_capture_root.expanduser().resolve()
    rebased = (resolved_root / capture_path.parts[-2] / capture_path.parts[-1]).resolve()
    if resolved_root not in rebased.parents:
        raise RuntimeError(f"Rebased capture path escapes capture root: {capture_path}")
    return rebased


def _comparison_metrics(report: ComparisonReport) -> dict[str, int | float]:
    aggregate = report.aggregate
    stock = aggregate.stock_external.median_ns
    internal = aggregate.instrumented_internal.median_ns
    return {
        "check_count": aggregate.check_count,
        "depth_count": aggregate.depth_count,
        "stock_external_median_ns": stock,
        "stock_external_mad_ns": aggregate.stock_external.mad_ns,
        "instrumented_external_median_ns": (aggregate.instrumented_external.median_ns),
        "instrumented_external_mad_ns": aggregate.instrumented_external.mad_ns,
        "external_overhead_median_ns": aggregate.external_overhead.median_ns,
        "external_overhead_mad_ns": aggregate.external_overhead.mad_ns,
        "external_overhead_pct": (
            aggregate.external_overhead.median_ns / stock * 100.0 if stock else 0.0
        ),
        "instrumented_internal_median_ns": internal,
        "instrumented_internal_mad_ns": aggregate.instrumented_internal.mad_ns,
        "array_envelope_median_ns": aggregate.array_envelope.median_ns,
        "array_envelope_mad_ns": aggregate.array_envelope.mad_ns,
        "non_array_residual_median_ns": aggregate.non_array_residual.median_ns,
        "non_array_residual_mad_ns": aggregate.non_array_residual.mad_ns,
        "array_fraction_pct": (
            aggregate.array_envelope.median_ns / internal * 100.0 if internal else 0.0
        ),
    }


def compare_garden_suite(
    raw_path: Path,
    comparison_dir: Path,
    builder_manifest: dict[str, Any],
    *,
    warmups: int,
    repetitions: int,
    timeout_seconds: float,
    downloaded_capture_root: Path | None = None,
    compare: Callable[..., ComparisonReport] = compare_capture,
) -> list[dict[str, Any]]:
    suite = load_json(raw_path)
    if not isinstance(suite, dict):
        raise RuntimeError(f"Garden result is not a JSON object: {raw_path}")

    raw_entries: list[tuple[str, dict[str, Any]]] = []
    for benchmark in suite.get("benchmarks", []):
        if not isinstance(benchmark, dict):
            continue
        example = str(benchmark.get("example", "unknown"))
        for result in benchmark.get("result", []):
            if isinstance(result, dict):
                raw_entries.append((example, result))
    if not raw_entries:
        raise RuntimeError(f"Garden produced no benchmark results: {raw_path}")

    entries: list[dict[str, Any]] = []
    for index, (example, result) in enumerate(raw_entries):
        result_type = _result_type(result.get("result"))
        capture_value = result.get("solver_capture_dir")
        capture_dir = _resolve_capture_dir(capture_value, downloaded_capture_root)
        entry: dict[str, Any] = {
            "example": _clean_example_name(example),
            "solver": result.get("solver"),
            "strategy": result.get("strategy"),
            "cost_function": result.get("cost_function"),
            "depth": result.get("depth"),
            "yardbird_result_type": result_type,
            "yardbird_run_time_ms": result.get("run_time"),
            "capture_dir": str(capture_dir) if capture_dir else None,
        }

        if result.get("solver") != "z3":
            entry.update(
                comparison_status="failed",
                comparison_error="Instrumentation comparison requires the Z3 solver backend",
            )
            entries.append(entry)
            continue

        capture_manifest = capture_dir / "manifest.json" if capture_dir else None
        if capture_manifest is None or not capture_manifest.is_file():
            if result_type in SOLVED_RESULT_TYPES:
                message = "successful Yardbird result has no completed solver capture"
                entry.update(comparison_status="failed", comparison_error=message)
            else:
                entry.update(
                    comparison_status="unavailable",
                    comparison_error=(
                        f"Yardbird result {result_type} did not produce a completed capture"
                    ),
                )
            entries.append(entry)
            continue

        capture_metadata = load_json(capture_manifest)
        if isinstance(capture_metadata, dict) and capture_metadata.get("benchmark_id"):
            entry["example"] = str(capture_metadata["benchmark_id"])

        output_path = comparison_dir / f"{index:05}.json"
        print(
            f"  [replay {index + 1}/{len(raw_entries)}] "
            f"{entry['strategy']} {entry['example']}",
            flush=True,
        )
        try:
            report = compare(
                capture_dir,
                builder_manifest,
                warmups=warmups,
                repetitions=repetitions,
                timeout_seconds=timeout_seconds,
            )
            write_comparison_report(output_path, report)
            entry.update(
                comparison_status="completed",
                comparison_path=str(output_path),
                metrics=_comparison_metrics(report),
            )
        except Exception as error:
            message = str(error)
            entry.update(comparison_status="failed", comparison_error=message)
        entries.append(entry)
    return entries


def compare_downloaded_aws_run(args: Any, manifest: dict[str, Any]) -> dict[str, Any]:
    """Replay captures downloaded from a completed AWS run on the local host."""
    if manifest.get("env") != "aws":
        raise RuntimeError(
            f"Run {manifest['run_id']} is not an AWS run: {manifest.get('env')}"
        )
    if manifest.get("status") != STATUS_COMPLETED:
        raise RuntimeError(
            f"Run {manifest['run_id']} is not complete: {manifest.get('status')}"
        )
    if args.warmups < 0:
        raise RuntimeError("--warmups must be nonnegative")
    if args.repetitions <= 0:
        raise RuntimeError("--repetitions must be positive")
    if args.replay_timeout <= 0:
        raise RuntimeError("--replay-timeout must be positive")
    if args.z3_build_jobs <= 0:
        raise RuntimeError("--z3-build-jobs must be positive")

    run_dir = Path(manifest["run_dir"])
    summary_path = run_dir / "instrumentation" / "comparisons.json"
    manifest["kind"] = "aws-instrumentation-comparison"
    manifest["instrumentation"] = {
        "warmups": args.warmups,
        "repetitions": args.repetitions,
        "replay_timeout_seconds": args.replay_timeout,
        "comparison_summary_path": str(summary_path),
    }
    save_manifest(manifest)

    z3_build_dir, builder_manifest = prepare_z3_build(args, run_dir)
    manifest["instrumentation"].update(
        {
            "z3_build_dir": str(z3_build_dir),
            "z3_builder_manifest": str(
                run_dir / "instrumentation" / "z3-builder-manifest.json"
            ),
        }
    )
    save_manifest(manifest)

    all_entries: list[dict[str, Any]] = []
    for subrun in manifest["subruns"]:
        run_type = str(subrun["benchmark_type"])
        raw_path = Path(subrun["result_path"])
        capture_root_value = subrun.get("capture_root")
        if not capture_root_value:
            raise RuntimeError(f"AWS subrun {run_type} has no downloaded capture root")
        capture_root = Path(capture_root_value)
        if not capture_root.is_dir():
            raise RuntimeError(
                f"AWS subrun {run_type} capture root does not exist: {capture_root}"
            )

        comparison_dir = ensure_dir(run_dir / "comparisons" / run_type)
        matrix_summary_path = comparison_dir / "summary.json"
        matrix_entries = compare_garden_suite(
            raw_path,
            comparison_dir,
            builder_manifest,
            warmups=args.warmups,
            repetitions=args.repetitions,
            timeout_seconds=args.replay_timeout,
            downloaded_capture_root=capture_root,
        )
        for entry in matrix_entries:
            entry["run_type"] = run_type
        all_entries.extend(matrix_entries)
        counts = _comparison_counts(matrix_entries)
        write_json(
            matrix_summary_path,
            {
                "run_id": manifest["run_id"],
                "run_type": run_type,
                "counts": counts,
                "entries": matrix_entries,
            },
        )
        subrun["comparison_summary_path"] = str(matrix_summary_path)
        subrun["comparison_counts"] = counts
        save_manifest(manifest)

    write_json(
        summary_path,
        {
            "run_id": manifest["run_id"],
            "run_types": manifest["benchmark_types"],
            "warmups": args.warmups,
            "repetitions": args.repetitions,
            "replay_timeout_seconds": args.replay_timeout,
            "counts": _comparison_counts(all_entries),
            "entries": all_entries,
        },
    )
    save_manifest(manifest)
    return manifest


def _comparison_counts(entries: list[dict[str, Any]]) -> dict[str, int]:
    counts = {"completed": 0, "unavailable": 0, "failed": 0}
    for entry in entries:
        status = str(entry.get("comparison_status"))
        counts[status] = counts.get(status, 0) + 1
    return counts


def launch_instrumentation_run(args: Any) -> dict[str, Any]:
    validate_new_run_id(args.run_id)
    if args.warmups < 0:
        raise RuntimeError("--warmups must be nonnegative")
    if args.repetitions <= 0:
        raise RuntimeError("--repetitions must be positive")
    if args.replay_timeout <= 0:
        raise RuntimeError("--replay-timeout must be positive")
    if args.z3_build_jobs <= 0:
        raise RuntimeError("--z3-build-jobs must be positive")
    config_path = Path(args.config).expanduser().resolve()
    if not config_path.is_file():
        raise FileNotFoundError(f"Garden config does not exist: {config_path}")

    manifest = base_manifest(
        args.run_id,
        "local",
        args.run_type,
        config_path,
        args.name,
    )
    manifest["kind"] = "instrumentation-comparison"
    run_dir = Path(manifest["run_dir"])
    summary_path = run_dir / "instrumentation" / "comparisons.json"
    manifest["instrumentation"] = {
        "warmups": args.warmups,
        "repetitions": args.repetitions,
        "replay_timeout_seconds": args.replay_timeout,
        "comparison_summary_path": str(summary_path),
    }
    save_manifest(manifest)

    all_entries: list[dict[str, Any]] = []
    try:
        ensure_garden_binary()
        z3_build_dir, builder_manifest = prepare_z3_build(args, run_dir)
        manifest["instrumentation"].update(
            {
                "z3_build_dir": str(z3_build_dir),
                "z3_builder_manifest": str(
                    run_dir / "instrumentation" / "z3-builder-manifest.json"
                ),
            }
        )
        save_manifest(manifest)

        for run_type in args.run_type:
            raw_dir = ensure_dir(run_dir / "raw" / run_type)
            raw_path = raw_dir / timestamp_filename()
            capture_root = run_dir / "captures" / run_type
            comparison_dir = ensure_dir(run_dir / "comparisons" / run_type)
            matrix_summary_path = comparison_dir / "summary.json"
            subrun = {
                "benchmark_type": run_type,
                "status": STATUS_RUNNING,
                "started_at": iso_now(),
                "completed_at": None,
                "result_path": str(raw_path),
                "capture_root": str(capture_root),
                "comparison_summary_path": str(matrix_summary_path),
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
                    str(config_path),
                    "--matrix",
                    run_type,
                    "--output",
                    str(raw_path),
                    "--profile",
                    "--solver-capture-root",
                    str(capture_root),
                ]
                if args.ranker_model:
                    command.extend(["--ranker-model", args.ranker_model])
                run_command(command, cwd=ROOT, capture_output=False)
                matrix_entries = compare_garden_suite(
                    raw_path,
                    comparison_dir,
                    builder_manifest,
                    warmups=args.warmups,
                    repetitions=args.repetitions,
                    timeout_seconds=args.replay_timeout,
                )
                for entry in matrix_entries:
                    entry["run_type"] = run_type
                all_entries.extend(matrix_entries)
                write_json(
                    matrix_summary_path,
                    {
                        "run_id": args.run_id,
                        "run_type": run_type,
                        "counts": _comparison_counts(matrix_entries),
                        "entries": matrix_entries,
                    },
                )
                counts = _comparison_counts(matrix_entries)
                subrun["comparison_counts"] = counts
                write_json(
                    summary_path,
                    {
                        "run_id": args.run_id,
                        "run_types": args.run_type,
                        "warmups": args.warmups,
                        "repetitions": args.repetitions,
                        "replay_timeout_seconds": args.replay_timeout,
                        "counts": _comparison_counts(all_entries),
                        "entries": all_entries,
                    },
                )
                if counts["failed"]:
                    failures = [
                        f"{entry['example']}: {entry.get('comparison_error', 'unknown error')}"
                        for entry in matrix_entries
                        if entry.get("comparison_status") == "failed"
                    ]
                    raise RuntimeError(
                        f"{counts['failed']} completed capture comparison(s) failed:\n"
                        + "\n".join(f"- {failure}" for failure in failures[:10])
                    )
                subrun["status"] = STATUS_COMPLETED
            except Exception as error:
                subrun["status"] = STATUS_FAILED
                subrun["error"] = str(error)
                raise
            finally:
                subrun["completed_at"] = iso_now()
                subrun["duration_seconds"] = round(
                    (now_local() - started).total_seconds(), 2
                )
                refresh_progress(manifest)
                save_manifest(manifest)

        write_json(
            summary_path,
            {
                "run_id": args.run_id,
                "run_types": args.run_type,
                "warmups": args.warmups,
                "repetitions": args.repetitions,
                "replay_timeout_seconds": args.replay_timeout,
                "counts": _comparison_counts(all_entries),
                "entries": all_entries,
            },
        )
        refresh_progress(manifest)
        save_manifest(manifest)
        return manifest
    except Exception:
        if manifest["status"] == STATUS_RUNNING:
            manifest["status"] = STATUS_FAILED
            manifest["completed_at"] = iso_now()
        save_manifest(manifest)
        raise
