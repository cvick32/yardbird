"""Run a capture through instrumented Z3 and validate its array summaries."""

from __future__ import annotations

import json
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .runner import BuilderBinaries, LoadedCapture, ReplayError, ReplayRunner


@dataclass(frozen=True)
class InstrumentedCheck:
    check_id: int
    result: str
    external_elapsed_ns: int
    check_elapsed_ns: int
    array_envelope_ns: int
    record: dict[str, Any]


@dataclass(frozen=True)
class InstrumentedReplay:
    binary: str
    checks: tuple[InstrumentedCheck, ...]


def profile_instrumented_replay(
    capture_dir: Path,
    builder_manifest: dict[str, Any],
    *,
    timeout_seconds: float = 60.0,
) -> InstrumentedReplay:
    """Replay once with summary profiling and validate every emitted record."""

    capture = LoadedCapture.load(capture_dir)
    binary = BuilderBinaries.from_manifest(builder_manifest).instrumented

    with tempfile.TemporaryDirectory(prefix="yardbird-z3-profile-") as temporary:
        output = Path(temporary) / "checks.jsonl"
        arguments = (
            "sat.smt=false",
            "smt.threads=1",
            "proof=false",
            "combined_solver.ignore_solver1=true",
            "smt.array.profile=true",
            f"smt.array.profile_output={output}",
        )
        replay = ReplayRunner(
            binary,
            label="instrumented",
            timeout_seconds=timeout_seconds,
            arguments=arguments,
        ).run(capture)
        if not output.is_file():
            raise ReplayError("instrumented: Z3 produced no array profile")
        records = _read_records(output)

    if len(records) != len(capture.checks):
        raise ReplayError(
            "instrumented: array profile count does not match the capture"
        )
    checks = []
    for indexed, external_elapsed, record in zip(
        capture.checks, replay.timings_ns, records
    ):
        _validate_record(indexed.check_id, indexed.expected_result, record)
        checks.append(
            InstrumentedCheck(
                check_id=indexed.check_id,
                result=indexed.expected_result,
                external_elapsed_ns=external_elapsed,
                check_elapsed_ns=record["check_elapsed_ns"],
                array_envelope_ns=record["array_envelope_ns"],
                record=record,
            )
        )
    return InstrumentedReplay(str(binary), tuple(checks))


def _read_records(path: Path) -> tuple[dict[str, Any], ...]:
    records = []
    for line_number, line in enumerate(path.read_text().splitlines(), start=1):
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise ReplayError(
                f"instrumented: invalid JSON on profile line {line_number}: {error}"
            ) from error
        if not isinstance(record, dict):
            raise ReplayError(
                f"instrumented: profile line {line_number} is not an object"
            )
        records.append(record)
    return tuple(records)


def _validate_record(
    check_id: int, expected_result: str, record: dict[str, Any]
) -> None:
    if record.get("check_ordinal") != check_id:
        raise ReplayError(
            f"instrumented: profile ordinal does not match check {check_id}"
        )
    if record.get("result") != expected_result:
        raise ReplayError(
            f"instrumented: profile result does not match check {check_id}"
        )
    for field in ("check_elapsed_ns", "array_envelope_ns"):
        if type(record.get(field)) is not int or record[field] < 0:
            raise ReplayError(f"instrumented: check {check_id} has invalid {field}")
    if record["array_envelope_ns"] > record["check_elapsed_ns"]:
        raise ReplayError(
            f"instrumented: check {check_id} array envelope exceeds check time"
        )
    forbidden = ("schema_version", "z3_revision", "profile_revision")
    present = [field for field in forbidden if field in record]
    if present:
        raise ReplayError(
            "instrumented: profile contains version labels: " + ", ".join(present)
        )
