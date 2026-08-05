"""Replay one Yardbird capture through the Z3 pair built by z3-builder."""

from __future__ import annotations

import json
import os
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SOLVER_RESULTS = {"sat", "unsat", "unknown"}


class ReplayError(RuntimeError):
    """The capture, builder output, or solver replay was invalid."""


@dataclass(frozen=True)
class SolverReplay:
    label: str
    binary: Path
    results: tuple[str, ...]


@dataclass(frozen=True)
class PairReplay:
    expected: tuple[str, ...]
    stock: SolverReplay
    instrumented: SolverReplay


@dataclass(frozen=True)
class _IndexedCheck:
    check_id: int
    depth: int
    refinement_id: int
    refinement_step: int
    setup_byte_start: int
    check_byte_start: int
    check_byte_end: int
    post_check_byte_end: int
    expected_result: str


def replay_build_pair(
    capture_dir: Path,
    builder_manifest: dict[str, Any],
    *,
    timeout_seconds: float = 60.0,
) -> PairReplay:
    """Replay a capture once through both binaries named by z3-builder."""

    if timeout_seconds <= 0:
        raise ReplayError("timeout must be positive")
    transcript, checks = _load_capture(capture_dir)
    binaries = _builder_binaries(builder_manifest)
    expected = tuple(check.expected_result for check in checks)
    stock = _replay(transcript, expected, "stock", binaries["stock"], timeout_seconds)
    instrumented = _replay(
        transcript,
        expected,
        "instrumented",
        binaries["instrumented"],
        timeout_seconds,
    )
    return PairReplay(expected, stock, instrumented)


def load_builder_manifest(build_dir: Path) -> dict[str, Any]:
    """Load an existing z3-builder output directory."""

    return _read_json(
        build_dir.expanduser().resolve() / "manifest.json", "z3-builder manifest"
    )


def _replay(
    transcript: bytes,
    expected: tuple[str, ...],
    label: str,
    binary: Path,
    timeout_seconds: float,
) -> SolverReplay:
    try:
        completed = subprocess.run(
            [str(binary), "-in", "-smt2"],
            input=transcript,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise ReplayError(
            f"{label}: replay timed out after {timeout_seconds:g} seconds"
        ) from error
    except OSError as error:
        raise ReplayError(f"{label}: could not start {binary}: {error}") from error

    stderr = completed.stderr.decode("utf-8", errors="replace").strip()
    stderr_suffix = "" if not stderr else f"; stderr: {stderr}"
    if completed.returncode != 0:
        raise ReplayError(
            f"{label}: solver exited with status {completed.returncode}{stderr_suffix}"
        )

    lines = tuple(
        line.strip()
        for line in completed.stdout.decode("utf-8", errors="replace").splitlines()
        if line.strip()
    )
    for output_line, result in enumerate(lines, start=1):
        if result not in SOLVER_RESULTS:
            raise ReplayError(
                f"{label}: output line {output_line} is not a solver result: "
                f"{result!r}{stderr_suffix}"
            )
    for check_id, expected_result in enumerate(expected):
        if check_id >= len(lines):
            raise ReplayError(
                f"{label}: check {check_id} produced no result; expected "
                f"{expected_result}{stderr_suffix}"
            )
        if lines[check_id] != expected_result:
            raise ReplayError(
                f"{label}: check {check_id} expected {expected_result}, "
                f"observed {lines[check_id]}{stderr_suffix}"
            )
    if len(lines) > len(expected):
        raise ReplayError(
            f"{label}: unexpected result after the final check: "
            f"{lines[len(expected)]}{stderr_suffix}"
        )
    return SolverReplay(label, binary, lines)


def _load_capture(capture_dir: Path) -> tuple[bytes, tuple[_IndexedCheck, ...]]:
    capture_dir = capture_dir.expanduser().resolve()
    manifest = _read_json(capture_dir / "manifest.json", "capture manifest")
    if manifest.get("complete") is not True:
        raise ReplayError("capture manifest is not complete")

    transcript = _capture_path(
        capture_dir, manifest.get("transcript"), "transcript"
    ).read_bytes()
    index = _read_json(
        _capture_path(capture_dir, manifest.get("index"), "journal index"),
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
    return transcript, checks


def _builder_binaries(manifest: dict[str, Any]) -> dict[str, Path]:
    if not isinstance(manifest, dict) or not isinstance(manifest.get("builds"), dict):
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
    return binaries


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


def _parse_check(raw: Any, expected_id: int) -> _IndexedCheck:
    if not isinstance(raw, dict):
        raise ReplayError(f"journal check {expected_id} is not an object")
    check = _IndexedCheck(
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
            f"journal check {expected_id} has invalid result "
            f"{check.expected_result!r}"
        )
    return check


def _integer(value: dict[str, Any], field: str) -> int:
    result = value.get(field)
    if type(result) is not int or result < 0:
        raise ReplayError(f"journal field {field} must be a nonnegative integer")
    return result


def _validate_boundaries(
    transcript: bytes, checks: tuple[_IndexedCheck, ...]
) -> None:
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
        if command != b"(check-sat)\n":
            raise ReplayError(
                f"check {check.check_id} boundary does not contain check-sat"
            )
        prior_end = check.post_check_byte_end
    if prior_end != len(transcript):
        raise ReplayError("final check boundary does not end the transcript")
