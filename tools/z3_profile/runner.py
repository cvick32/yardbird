"""Validated capture loading and persistent solver replay."""

from __future__ import annotations

import json
import os
import selectors
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SOLVER_RESULTS = {"sat", "unsat", "unknown"}


class ReplayError(RuntimeError):
    """The capture, builder output, or solver replay was invalid."""


@dataclass(frozen=True)
class IndexedCheck:
    check_id: int
    depth: int
    refinement_id: int
    refinement_step: int
    setup_byte_start: int
    check_byte_start: int
    check_byte_end: int
    post_check_byte_end: int
    expected_result: str


@dataclass(frozen=True)
class ProfileCheck:
    instances_total: int
    instances_added_since_previous_check: int


@dataclass(frozen=True)
class LoadedCapture:
    """A validated capture whose index is aligned with its transcript."""

    directory: Path
    transcript: bytes
    checks: tuple[IndexedCheck, ...]
    manifest: dict[str, Any]

    @classmethod
    def load(cls, capture_dir: Path) -> LoadedCapture:
        directory = capture_dir.expanduser().resolve()
        manifest = _read_json(directory / "manifest.json", "capture manifest")
        if manifest.get("complete") is not True:
            raise ReplayError("capture manifest is not complete")

        transcript = _capture_path(
            directory, manifest.get("transcript"), "transcript"
        ).read_bytes()
        index = _read_json(
            _capture_path(directory, manifest.get("index"), "journal index"),
            "journal index",
        )
        raw_checks = index.get("checks")
        if not isinstance(raw_checks, list) or not raw_checks:
            raise ReplayError("journal index contains no checks")
        if manifest.get("check_count") != len(raw_checks):
            raise ReplayError("capture check count does not match the journal index")

        checks = tuple(
            _parse_check(raw_check, check_id)
            for check_id, raw_check in enumerate(raw_checks)
        )
        _validate_boundaries(transcript, checks)
        return cls(directory, transcript, checks, manifest)

    @property
    def expected_results(self) -> tuple[str, ...]:
        return tuple(check.expected_result for check in self.checks)

    def load_profile_checks(self) -> tuple[ProfileCheck, ...]:
        profile = _read_json(
            _capture_path(
                self.directory,
                self.manifest.get("profile"),
                "Yardbird profile",
            ),
            "Yardbird profile",
        )
        records = profile.get("solver_checks")
        if not isinstance(records, list) or len(records) != len(self.checks):
            raise ReplayError("Yardbird profile check count does not match the index")

        result = []
        for check, record in zip(self.checks, records):
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
            for field in (
                "instances_total",
                "instances_added_since_previous_check",
            ):
                if type(record.get(field)) is not int or record[field] < 0:
                    raise ReplayError(
                        f"Yardbird profile check {check.check_id} has invalid {field}"
                    )
            result.append(
                ProfileCheck(
                    instances_total=record["instances_total"],
                    instances_added_since_previous_check=record[
                        "instances_added_since_previous_check"
                    ],
                )
            )
        return tuple(result)


@dataclass(frozen=True)
class BuilderBinaries:
    stock: Path
    instrumented: Path

    @classmethod
    def from_manifest(cls, manifest: dict[str, Any]) -> BuilderBinaries:
        if not isinstance(manifest, dict) or not isinstance(
            manifest.get("builds"), dict
        ):
            raise ReplayError("z3-builder input has no builds object")
        builds = manifest["builds"]
        binaries = {}
        for label in ("stock", "instrumented"):
            build = builds.get(label)
            value = build.get("binary") if isinstance(build, dict) else None
            if not isinstance(value, str) or not value:
                raise ReplayError(f"z3-builder input has no {label} binary")
            path = Path(value).expanduser().resolve()
            if not path.is_file() or not os.access(path, os.X_OK):
                raise ReplayError(f"{label} binary is not executable: {path}")
            binaries[label] = path
        return cls(stock=binaries["stock"], instrumented=binaries["instrumented"])


@dataclass(frozen=True)
class ReplayRun:
    results: tuple[str, ...]
    timings_ns: tuple[int, ...]


class ReplayRunner:
    """Run one validated capture through one persistent solver process."""

    def __init__(
        self,
        binary: Path,
        *,
        label: str,
        timeout_seconds: float = 60.0,
        arguments: tuple[str, ...] = (),
    ) -> None:
        if timeout_seconds <= 0:
            raise ReplayError("timeout must be positive")
        self.binary = binary.expanduser().resolve()
        self.label = label
        self.timeout_seconds = timeout_seconds
        self.arguments = arguments

    def run(self, capture: LoadedCapture) -> ReplayRun:
        solver = _InteractiveSolver(
            self.binary, label=self.label, arguments=self.arguments
        )
        results = []
        timings = []
        try:
            for check in capture.checks:
                solver.write(
                    capture.transcript[check.setup_byte_start : check.check_byte_start],
                    check.check_id,
                )
                started = time.perf_counter_ns()
                solver.write(
                    capture.transcript[check.check_byte_start : check.check_byte_end],
                    check.check_id,
                )
                observed = solver.result(check.check_id, self.timeout_seconds)
                timings.append(time.perf_counter_ns() - started)
                if observed != check.expected_result:
                    raise ReplayError(
                        f"{self.label}: check {check.check_id} expected "
                        f"{check.expected_result}, observed {observed}"
                    )
                results.append(observed)
                solver.write(
                    capture.transcript[
                        check.check_byte_end : check.post_check_byte_end
                    ],
                    check.check_id,
                )
            solver.finish(self.timeout_seconds)
        finally:
            solver.close()
        return ReplayRun(tuple(results), tuple(timings))


class _InteractiveSolver:
    def __init__(
        self,
        binary: Path,
        *,
        label: str,
        arguments: tuple[str, ...],
    ) -> None:
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
            raise ReplayError(f"{label}: could not start {binary}: {error}") from error
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


def read_json_object(path: Path, label: str) -> dict[str, Any]:
    """Read a JSON object with replay-specific error reporting."""

    return _read_json(path, label)


def _read_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except OSError as error:
        raise ReplayError(f"could not read {label} {path}: {error}") from error
    except json.JSONDecodeError as error:
        raise ReplayError(f"{label} is invalid JSON: {error}") from error
    if not isinstance(value, dict):
        raise ReplayError(f"{label} must contain a JSON object")
    return value


def _capture_path(capture_dir: Path, value: Any, label: str) -> Path:
    if not isinstance(value, str) or not value:
        raise ReplayError(f"capture manifest has no {label} path")
    path = (capture_dir / value).resolve()
    if path != capture_dir and capture_dir not in path.parents:
        raise ReplayError(f"{label} path escapes the capture directory")
    if not path.is_file():
        raise ReplayError(f"{label} does not exist: {path}")
    return path


def _parse_check(raw: Any, expected_id: int) -> IndexedCheck:
    if not isinstance(raw, dict):
        raise ReplayError(f"journal check {expected_id} is not an object")
    check = IndexedCheck(
        check_id=_integer(raw, "check_id"),
        depth=_integer(raw, "depth"),
        refinement_id=_integer(raw, "refinement_id"),
        refinement_step=_integer(raw, "refinement_step"),
        setup_byte_start=_integer(raw, "setup_byte_start"),
        check_byte_start=_integer(raw, "check_byte_start"),
        check_byte_end=_integer(raw, "check_byte_end"),
        post_check_byte_end=_integer(raw, "post_check_byte_end"),
        expected_result=str(raw.get("expected_result")),
    )
    if check.check_id != expected_id:
        raise ReplayError(
            f"journal check IDs are not contiguous: expected {expected_id}, "
            f"observed {check.check_id}"
        )
    if check.expected_result not in SOLVER_RESULTS:
        raise ReplayError(
            f"journal check {expected_id} has invalid result {check.expected_result!r}"
        )
    return check


def _integer(value: dict[str, Any], field: str) -> int:
    result = value.get(field)
    if type(result) is not int or result < 0:
        raise ReplayError(f"journal field {field} must be a nonnegative integer")
    return result


def _validate_boundaries(transcript: bytes, checks: tuple[IndexedCheck, ...]) -> None:
    prior_end = 0
    for check in checks:
        valid = (
            check.setup_byte_start == prior_end
            and check.setup_byte_start <= check.check_byte_start
            and check.check_byte_start < check.check_byte_end
            and check.check_byte_end <= check.post_check_byte_end
            and check.post_check_byte_end <= len(transcript)
        )
        if not valid:
            raise ReplayError(f"check {check.check_id} has invalid byte boundaries")
        command = transcript[check.check_byte_start : check.check_byte_end]
        is_check_sat = command == b"(check-sat)\n"
        is_check_sat_assuming = command.startswith(b"(check-sat-assuming ") and command.endswith(
            b")\n"
        )
        if not (is_check_sat or is_check_sat_assuming):
            raise ReplayError(
                f"check {check.check_id} boundary does not contain check-sat"
            )
        prior_end = check.post_check_byte_end
    if prior_end != len(transcript):
        raise ReplayError("final check boundary does not end the transcript")
