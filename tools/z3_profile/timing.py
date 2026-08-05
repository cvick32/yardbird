"""Repeated stock-Z3 timing for a captured Yardbird solver session."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from .distribution import TimingDistribution
from .runner import (
    BuilderBinaries,
    IndexedCheck,
    LoadedCapture,
    ProfileCheck,
    ReplayError,
    ReplayRunner,
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
    timing: TimingDistribution


@dataclass(frozen=True)
class DepthTiming:
    depth: int
    check_ids: tuple[int, ...]
    refinement_ids: tuple[int, ...]
    refinement_steps: tuple[int, ...]
    results: tuple[str, ...]
    instances_total: int
    instances_added: int
    timing: TimingDistribution


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
                f"median={check.timing.median_ns / 1_000_000:.3f}ms "
                f"mad={check.timing.mad_ns / 1_000_000:.3f}ms "
                f"instances={check.instances_total} "
                f"(+{check.instances_added_since_previous_check})"
            )
        lines.append("depths:")
        for depth in self.depths:
            lines.append(
                f"  {depth.depth}: checks={','.join(map(str, depth.check_ids))} "
                f"median={depth.timing.median_ns / 1_000_000:.3f}ms "
                f"mad={depth.timing.mad_ns / 1_000_000:.3f}ms "
                f"instances={depth.instances_total} (+{depth.instances_added})"
            )
        return "\n".join(lines)


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

    capture = LoadedCapture.load(capture_dir)
    profile_checks = capture.load_profile_checks()
    stock_binary = BuilderBinaries.from_manifest(builder_manifest).stock
    runner = ReplayRunner(stock_binary, label="stock", timeout_seconds=timeout_seconds)

    for _ in range(warmups):
        runner.run(capture)
    samples = tuple(runner.run(capture).timings_ns for _ in range(repetitions))
    return aggregate_stock_timings(
        capture,
        stock_binary,
        warmups,
        repetitions,
        profile_checks,
        samples,
    )


def write_timing_report(path: Path, report: TimingReport) -> None:
    path = path.expanduser()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report.to_dict(), indent=2, sort_keys=True) + "\n")


def aggregate_stock_timings(
    capture: LoadedCapture,
    stock_binary: Path,
    warmups: int,
    repetitions: int,
    profile_checks: tuple[ProfileCheck, ...],
    samples: tuple[tuple[int, ...], ...],
) -> TimingReport:
    checks = capture.checks
    if len(samples) != repetitions or any(
        len(sample) != len(checks) for sample in samples
    ):
        raise ReplayError("timing sample shape does not match the capture")

    check_reports = []
    for index, (check, profile) in enumerate(zip(checks, profile_checks)):
        check_samples = tuple(repetition[index] for repetition in samples)
        check_reports.append(
            CheckTiming(
                check_id=check.check_id,
                depth=check.depth,
                refinement_id=check.refinement_id,
                refinement_step=check.refinement_step,
                result=check.expected_result,
                instances_total=profile.instances_total,
                instances_added_since_previous_check=(
                    profile.instances_added_since_previous_check
                ),
                timing=TimingDistribution.from_samples(check_samples),
            )
        )

    depth_indices: dict[int, list[int]] = {}
    for index, check in enumerate(checks):
        depth_indices.setdefault(check.depth, []).append(index)
    depth_reports = tuple(
        _aggregate_depth(depth, indices, checks, profile_checks, samples)
        for depth, indices in depth_indices.items()
    )

    return TimingReport(
        capture_dir=str(capture.directory),
        stock_binary=str(stock_binary),
        warmups=warmups,
        repetitions=repetitions,
        checks=tuple(check_reports),
        depths=depth_reports,
    )


def _aggregate_depth(
    depth: int,
    indices: list[int],
    checks: tuple[IndexedCheck, ...],
    profiles: tuple[ProfileCheck, ...],
    samples: tuple[tuple[int, ...], ...],
) -> DepthTiming:
    depth_samples = tuple(
        sum(repetition[index] for index in indices) for repetition in samples
    )
    return DepthTiming(
        depth=depth,
        check_ids=tuple(checks[index].check_id for index in indices),
        refinement_ids=tuple(checks[index].refinement_id for index in indices),
        refinement_steps=tuple(checks[index].refinement_step for index in indices),
        results=tuple(checks[index].expected_result for index in indices),
        instances_total=profiles[indices[-1]].instances_total,
        instances_added=sum(
            profiles[index].instances_added_since_previous_check for index in indices
        ),
        timing=TimingDistribution.from_samples(depth_samples),
    )
