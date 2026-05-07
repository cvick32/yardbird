"""Run Yardbird over generated benchmarks."""

from __future__ import annotations

from pathlib import Path
import subprocess
import time

from .manifests import RunEntry, write_run_manifest


def run_benchmark(
    benchmark_path: Path,
    *,
    yardbird_bin: Path,
    strategy: str,
    depth: int,
    cost_function: str | None = None,
    timeout_seconds: int = 10,
) -> RunEntry:
    command = [
        str(yardbird_bin),
        "--filename",
        str(benchmark_path),
        "--strategy",
        strategy,
        "--depth",
        str(depth),
        "--json-output",
    ]
    if cost_function is not None:
        command.extend(["--cost-function", cost_function])

    started = time.perf_counter()
    proc = subprocess.run(
        command,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
        check=False,
    )
    duration = time.perf_counter() - started
    status = "ok" if proc.returncode == 0 else "error"
    return RunEntry(
        benchmark_name=benchmark_path.stem,
        benchmark_path=str(benchmark_path),
        strategy=strategy,
        cost_function=cost_function,
        depth=depth,
        duration_seconds=duration,
        exit_code=proc.returncode,
        status=status,
    )


def run_corpus(
    corpus_dir: Path,
    *,
    yardbird_bin: Path,
    strategy: str,
    depth: int,
    cost_function: str | None = None,
    timeout_seconds: int = 10,
) -> list[RunEntry]:
    benchmarks = sorted((corpus_dir / "benchmarks").glob("*.vmt"))
    return [
        run_benchmark(
            benchmark,
            yardbird_bin=yardbird_bin,
            strategy=strategy,
            depth=depth,
            cost_function=cost_function,
            timeout_seconds=timeout_seconds,
        )
        for benchmark in benchmarks
    ]


def write_runs(path: Path, entries: list[RunEntry]) -> None:
    write_run_manifest(path, entries)
