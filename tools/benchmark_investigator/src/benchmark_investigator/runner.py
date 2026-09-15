"""Execute one pinned binary; the agent never constructs a shell command."""

import asyncio
import os
import re
import signal
import time
from pathlib import Path

from .artifacts import now, read_json, sha256, write_json
from .models import ExperimentConfig


async def stop_process(process):
    if process.returncode is None:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    await process.wait()


def command(
    binary: Path,
    benchmark: Path,
    config: ExperimentConfig,
    depth: int,
    timeout_secs: int,
    ranker: Path | None = None,
) -> list[str]:
    args = [
        str(binary),
        "--filename",
        str(benchmark),
        "--depth",
        str(depth),
        "--wall-timeout-secs",
        str(timeout_secs),
        "--profile",
        "--json-output",
        "--solver",
        "z3",
        "--theory",
        "array",
        "--instantiation-strategy",
        "full-unroll",
    ]
    for key, value in config.model_dump().items():
        args.extend(["--" + key.replace("_", "-"), str(value)])
    if config.cost_function == "logistic-regression":
        if ranker is None:
            raise ValueError("logistic-regression requires a pinned ranker model")
        args.extend(["--ranker-model", str(ranker)])
    return args


async def execute_run(
    *,
    directory: Path,
    run_id: str,
    benchmark_id: str,
    ordinal: int,
    binary: Path,
    binary_hash: str,
    benchmark: Path,
    benchmark_hash: str,
    source_root: Path,
    config: ExperimentConfig,
    depth: int,
    timeout_secs: int,
    kill_grace_secs: int,
    parent_run_id: str | None = None,
    action: dict | None = None,
    ranker: Path | None = None,
) -> dict:
    if sha256(binary) != binary_hash or sha256(benchmark) != benchmark_hash:
        raise ValueError("Pinned executable or benchmark changed")
    args = command(binary, benchmark, config, depth, timeout_secs, ranker)
    directory.mkdir(parents=True, exist_ok=False)
    write_json(directory / "config.json", config.model_dump())
    write_json(directory / "action.json", action or {"action": "MANDATORY"})
    metadata = {
        "run_id": run_id,
        "benchmark_id": benchmark_id,
        "ordinal": ordinal,
        "parent_run_id": parent_run_id,
        "command": args,
        "started_at": now(),
        "target_depth": depth,
        "timeout_secs": timeout_secs,
        "binary_sha256": binary_hash,
        "benchmark_sha256": benchmark_hash,
    }
    write_json(directory / "metadata.json", metadata | {"state": "running"})
    start = time.monotonic()
    reason = None
    error = None
    returncode = None
    process = None
    try:
        with (
            (directory / "stdout.log").open("wb") as stdout,
            (directory / "stderr.log").open("wb") as stderr,
        ):
            process = await asyncio.create_subprocess_exec(
                *args, cwd=source_root, stdout=stdout, stderr=stderr, start_new_session=True
            )
            try:
                await asyncio.wait_for(process.wait(), timeout_secs + kill_grace_secs)
            except TimeoutError:
                reason = "external_timeout"
                await stop_process(process)
            returncode = process.returncode
    except asyncio.CancelledError:
        if process is not None:
            await stop_process(process)
        reason = "interrupted"
        raise
    except OSError as exc:
        reason, error = "spawn_error", str(exc)
    finally:
        metadata.update(
            finished_at=now(),
            wall_time_secs=time.monotonic() - start,
            returncode=process.returncode if process is not None else returncode,
            state="finished",
            termination_reason=reason,
            error=error,
        )
        write_json(directory / "metadata.json", metadata)
    result = None
    try:
        candidate = read_json(directory / "stdout.log")
        if not isinstance(candidate, dict) or not isinstance(candidate.get("profiling"), dict):
            raise TypeError("stdout is not a Yardbird result with profiling")
        result = candidate
    except (OSError, ValueError, TypeError) as exc:
        error = error or str(exc)
    progress = (result or {}).get("run_progress") or {}
    if reason is None:
        reason = progress.get("termination_reason")
        if reason is None:
            reason = "counterexample" if (result or {}).get("counterexample") else "invalid_result"
        if returncode and reason in {"depth_limit", "proof"}:
            reason, error = "process_error", "Nonzero exit disagrees with success result"
    stderr_text = (
        (directory / "stderr.log").read_text(errors="replace")
        if (directory / "stderr.log").exists()
        else ""
    )
    version = re.search(r"Z3 version:\s*([^\r\n]+)", stderr_text)
    metadata.update(
        termination_reason=reason,
        error=progress.get("error") or error,
        profile_available=result is not None,
        z3_version=version.group(1) if version else None,
    )
    write_json(directory / "result.json", result)
    write_json(directory / "profile.json", result.get("profiling") if result else None)
    write_json(directory / "metadata.json", metadata)
    return metadata
