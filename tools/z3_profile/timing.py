"""Repeated stock-Z3 timing for a captured Yardbird solver session."""

from __future__ import annotations

import json
import os
import selectors
import statistics
import subprocess
import tempfile
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from .replay import (
    SOLVER_RESULTS,
    ReplayError,
    _IndexedCheck,
    _builder_binaries,
    _capture_path,
    _load_capture,
    _read_json,
)


@dataclass(frozen=True)
class CheckTiming:
    check_id: int
    depth: int
    refinement_id: int
    refinement_step: int
    result: str
    instances_total: int
    instances_added_since_previous_check: int
    samples_ns: tuple[int, ...]
    median_ns: int
    mad_ns: int


@dataclass(frozen=True)
class DepthTiming:
    depth: int
    check_ids: tuple[int, ...]
    results: tuple[str, ...]
    samples_ns: tuple[int, ...]
    median_ns: int
    mad_ns: int


@dataclass(frozen=True)
class TimingReport:
    capture_dir: str
    stock_binary: str
    warmups: int
    repetitions: int
    checks: tuple[CheckTiming, ...]
    depths: tuple[DepthTiming, ...]

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def summary(self) -> str:
        lines = [
            f"stock timing: {self.repetitions} repetitions after {self.warmups} warmups",
            "checks:",
        ]
        for check in self.checks:
            lines.append(
                f"  {check.check_id}: depth={check.depth} "
                f"refinement={check.refinement_step} result={check.result} "
                f"median={check.median_ns / 1_000_000:.3f}ms "
                f"mad={check.mad_ns / 1_000_000:.3f}ms "
                f"instances={check.instances_total} "
                f"(+{check.instances_added_since_previous_check})"
            )
        lines.append("depths:")
        for depth in self.depths:
            lines.append(
                f"  {depth.depth}: checks={','.join(map(str, depth.check_ids))} "
                f"median={depth.median_ns / 1_000_000:.3f}ms "
                f"mad={depth.mad_ns / 1_000_000:.3f}ms"
            )
        return "\n".join(lines)


class _InteractiveSolver:
    def __init__(
        self,
        binary: Path,
        *,
        label: str = "stock",
        arguments: tuple[str, ...] = (),
    ):
        self.label = label
        self._stderr = tempfile.TemporaryFile()
        try:
            self.process = subprocess.Popen(
                [str(binary), *arguments, "-in", "-smt2"],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=self._stderr,
                bufsize=0,
            )
        except OSError as error:
            self._stderr.close()
            raise ReplayError(
                f"{label}: could not start {binary}: {error}"
            ) from error
        assert self.process.stdin is not None
        assert self.process.stdout is not None
        self._selector = selectors.DefaultSelector()
        self._selector.register(self.process.stdout, selectors.EVENT_READ)
        self._buffer = b""

    def write(self, chunk: bytes, check_id: int | None = None) -> None:
        if not chunk:
            return
        if self.process.poll() is not None:
            self._raise_exit("exited before accepting input", check_id)
        try:
            assert self.process.stdin is not None
            self.process.stdin.write(chunk)
            self.process.stdin.flush()
        except (BrokenPipeError, OSError) as error:
            self._raise_exit(f"input pipe failed: {error}", check_id)

    def result(self, check_id: int, timeout_seconds: float) -> str:
        deadline = time.monotonic() + timeout_seconds
        while b"\n" not in self._buffer:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise ReplayError(
                    f"{self.label}: check {check_id} timed out after "
                    f"{timeout_seconds:g} seconds{self._stderr_suffix()}"
                )
            if not self._selector.select(remaining):
                continue
            assert self.process.stdout is not None
            chunk = os.read(self.process.stdout.fileno(), 4096)
            if not chunk:
                self._raise_exit("exited before returning a result", check_id)
            self._buffer += chunk

        line, self._buffer = self._buffer.split(b"\n", 1)
        result = line.decode("utf-8", errors="replace").strip()
        if result not in SOLVER_RESULTS:
            raise ReplayError(
                f"{self.label}: check {check_id} returned invalid output "
                f"{result!r}{self._stderr_suffix()}"
            )
        return result

    def finish(self, timeout_seconds: float) -> None:
        self.write(b"(exit)\n")
        assert self.process.stdin is not None
        self.process.stdin.close()
        try:
            exit_code = self.process.wait(timeout=timeout_seconds)
        except subprocess.TimeoutExpired as error:
            raise ReplayError(
                f"{self.label}: solver did not exit after replay"
            ) from error
        if exit_code != 0:
            raise ReplayError(
                f"{self.label}: solver exited with status "
                f"{exit_code}{self._stderr_suffix()}"
            )

    def close(self) -> None:
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=0.2)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait()
        self._selector.close()
        for stream in (self.process.stdin, self.process.stdout):
            if stream is not None and not stream.closed:
                try:
                    stream.close()
                except BrokenPipeError:
                    pass
        self._stderr.close()

    def _raise_exit(self, message: str, check_id: int | None) -> None:
        location = "" if check_id is None else f" during check {check_id}"
        status = self.process.poll()
        status_text = "" if status is None else f" with status {status}"
        raise ReplayError(
            f"{self.label}: solver {message}{location}{status_text}"
            f"{self._stderr_suffix()}"
        )

    def _stderr_suffix(self) -> str:
        self._stderr.flush()
        self._stderr.seek(0)
        stderr = self._stderr.read().decode("utf-8", errors="replace").strip()
        self._stderr.seek(0, os.SEEK_END)
        return "" if not stderr else f"; stderr: {stderr}"


def time_stock_replay(
    capture_dir: Path,
    builder_manifest: dict[str, Any],
    *,
    warmups: int = 3,
    repetitions: int = 15,
    timeout_seconds: float = 60.0,
) -> TimingReport:
    """Measure repeated stock replays and aggregate checks and depths."""

    if warmups < 0:
        raise ReplayError("warmups must be nonnegative")
    if repetitions <= 0:
        raise ReplayError("repetitions must be positive")
    if timeout_seconds <= 0:
        raise ReplayError("timeout must be positive")

    capture_dir = capture_dir.expanduser().resolve()
    transcript, checks = _load_capture(capture_dir)
    profile_checks = _load_profile_checks(capture_dir, checks)
    stock_binary = _builder_binaries(builder_manifest)["stock"]

    for _ in range(warmups):
        _run_repetition(transcript, checks, stock_binary, timeout_seconds)
    samples = tuple(
        _run_repetition(transcript, checks, stock_binary, timeout_seconds)
        for _ in range(repetitions)
    )
    return _aggregate(
        capture_dir,
        stock_binary,
        warmups,
        repetitions,
        checks,
        profile_checks,
        samples,
    )


def write_timing_report(path: Path, report: TimingReport) -> None:
    path = path.expanduser()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report.to_dict(), indent=2, sort_keys=True) + "\n")


def _run_repetition(
    transcript: bytes,
    checks: tuple[_IndexedCheck, ...],
    binary: Path,
    timeout_seconds: float,
    *,
    label: str = "stock",
    arguments: tuple[str, ...] = (),
) -> tuple[int, ...]:
    solver = _InteractiveSolver(binary, label=label, arguments=arguments)
    timings = []
    try:
        for check in checks:
            solver.write(
                transcript[check.setup_byte_start : check.check_byte_start],
                check.check_id,
            )
            started = time.perf_counter_ns()
            solver.write(
                transcript[check.check_byte_start : check.check_byte_end],
                check.check_id,
            )
            observed = solver.result(check.check_id, timeout_seconds)
            elapsed = time.perf_counter_ns() - started
            if observed != check.expected_result:
                raise ReplayError(
                    f"{label}: check {check.check_id} expected "
                    f"{check.expected_result}, observed {observed}"
                )
            timings.append(elapsed)
            solver.write(
                transcript[check.check_byte_end : check.post_check_byte_end],
                check.check_id,
            )
        solver.finish(timeout_seconds)
    finally:
        solver.close()
    return tuple(timings)


def _load_profile_checks(
    capture_dir: Path, checks: tuple[_IndexedCheck, ...]
) -> tuple[dict[str, Any], ...]:
    manifest = _read_json(capture_dir / "manifest.json", "capture manifest")
    profile = _read_json(
        _capture_path(capture_dir, manifest.get("profile"), "Yardbird profile"),
        "Yardbird profile",
    )
    records = profile.get("solver_checks")
    if not isinstance(records, list) or len(records) != len(checks):
        raise ReplayError("Yardbird profile check count does not match the index")
    for check, record in zip(checks, records):
        if not isinstance(record, dict):
            raise ReplayError(f"Yardbird profile check {check.check_id} is invalid")
        if (
            record.get("check_id") != check.check_id
            or record.get("depth") != check.depth
            or record.get("refinement_id") != check.refinement_id
            or record.get("refinement_step") != check.refinement_step
            or record.get("result") != check.expected_result
        ):
            raise ReplayError(
                f"Yardbird profile check {check.check_id} does not match the index"
            )
        for field in ("instances_total", "instances_added_since_previous_check"):
            if type(record.get(field)) is not int or record[field] < 0:
                raise ReplayError(
                    f"Yardbird profile check {check.check_id} has invalid {field}"
                )
    return tuple(records)


def _aggregate(
    capture_dir: Path,
    stock_binary: Path,
    warmups: int,
    repetitions: int,
    checks: tuple[_IndexedCheck, ...],
    profile_checks: tuple[dict[str, Any], ...],
    samples: tuple[tuple[int, ...], ...],
) -> TimingReport:
    if len(samples) != repetitions or any(len(sample) != len(checks) for sample in samples):
        raise ReplayError("timing sample shape does not match the capture")

    check_reports = []
    for index, (check, profile) in enumerate(zip(checks, profile_checks)):
        check_samples = tuple(repetition[index] for repetition in samples)
        median, mad = _median_and_mad(check_samples)
        check_reports.append(
            CheckTiming(
                check_id=check.check_id,
                depth=check.depth,
                refinement_id=check.refinement_id,
                refinement_step=check.refinement_step,
                result=check.expected_result,
                instances_total=profile["instances_total"],
                instances_added_since_previous_check=profile[
                    "instances_added_since_previous_check"
                ],
                samples_ns=check_samples,
                median_ns=median,
                mad_ns=mad,
            )
        )

    depth_indices: dict[int, list[int]] = {}
    for index, check in enumerate(checks):
        depth_indices.setdefault(check.depth, []).append(index)
    depth_reports = []
    for depth, indices in depth_indices.items():
        depth_samples = tuple(
            sum(repetition[index] for index in indices) for repetition in samples
        )
        median, mad = _median_and_mad(depth_samples)
        depth_reports.append(
            DepthTiming(
                depth=depth,
                check_ids=tuple(checks[index].check_id for index in indices),
                results=tuple(checks[index].expected_result for index in indices),
                samples_ns=depth_samples,
                median_ns=median,
                mad_ns=mad,
            )
        )

    return TimingReport(
        capture_dir=str(capture_dir),
        stock_binary=str(stock_binary),
        warmups=warmups,
        repetitions=repetitions,
        checks=tuple(check_reports),
        depths=tuple(depth_reports),
    )


def _median_and_mad(samples: tuple[int, ...]) -> tuple[int, int]:
    median = int(statistics.median(samples))
    mad = int(statistics.median(abs(sample - median) for sample in samples))
    return median, mad
