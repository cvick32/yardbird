"""Join stock replay timings with instrumented-Z3 array summaries."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from .instrumented import InstrumentedReplay, profile_instrumented_replay
from .replay import ReplayError, _builder_binaries, _load_capture
from .timing import (
    TimingReport,
    _aggregate as aggregate_stock_timings,
    _load_profile_checks,
    _median_and_mad,
    _run_repetition,
)


@dataclass(frozen=True)
class CheckComparison:
    check_id: int
    depth: int
    refinement_id: int
    refinement_step: int
    result: str
    instances_total: int
    instances_added_since_previous_check: int
    stock_external_samples_ns: tuple[int, ...]
    stock_external_median_ns: int
    stock_external_mad_ns: int
    instrumented_external_samples_ns: tuple[int, ...]
    instrumented_external_median_ns: int
    instrumented_external_mad_ns: int
    instrumented_internal_samples_ns: tuple[int, ...]
    instrumented_internal_median_ns: int
    instrumented_internal_mad_ns: int
    array_envelope_samples_ns: tuple[int, ...]
    array_envelope_median_ns: int
    array_envelope_mad_ns: int
    non_array_residual_samples_ns: tuple[int, ...]
    non_array_residual_median_ns: int
    non_array_residual_mad_ns: int


@dataclass(frozen=True)
class DepthComparison:
    depth: int
    check_ids: tuple[int, ...]
    results: tuple[str, ...]
    stock_external_samples_ns: tuple[int, ...]
    stock_external_median_ns: int
    stock_external_mad_ns: int
    instrumented_external_samples_ns: tuple[int, ...]
    instrumented_external_median_ns: int
    instrumented_external_mad_ns: int
    instrumented_internal_samples_ns: tuple[int, ...]
    instrumented_internal_median_ns: int
    instrumented_internal_mad_ns: int
    array_envelope_samples_ns: tuple[int, ...]
    array_envelope_median_ns: int
    array_envelope_mad_ns: int
    non_array_residual_samples_ns: tuple[int, ...]
    non_array_residual_median_ns: int
    non_array_residual_mad_ns: int


@dataclass(frozen=True)
class AggregateComparison:
    check_count: int
    depth_count: int
    stock_external_samples_ns: tuple[int, ...]
    stock_external_median_ns: int
    stock_external_mad_ns: int
    instrumented_external_samples_ns: tuple[int, ...]
    instrumented_external_median_ns: int
    instrumented_external_mad_ns: int
    external_overhead_samples_ns: tuple[int, ...]
    external_overhead_median_ns: int
    external_overhead_mad_ns: int
    instrumented_internal_samples_ns: tuple[int, ...]
    instrumented_internal_median_ns: int
    instrumented_internal_mad_ns: int
    array_envelope_samples_ns: tuple[int, ...]
    array_envelope_median_ns: int
    array_envelope_mad_ns: int
    non_array_residual_samples_ns: tuple[int, ...]
    non_array_residual_median_ns: int
    non_array_residual_mad_ns: int


@dataclass(frozen=True)
class ComparisonReport:
    capture_dir: str
    stock_binary: str
    instrumented_binary: str
    warmups: int
    repetitions: int
    aggregate: AggregateComparison
    checks: tuple[CheckComparison, ...]
    depths: tuple[DepthComparison, ...]

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def summary(self) -> str:
        aggregate = self.aggregate
        overhead = (
            aggregate.external_overhead_median_ns
            / aggregate.stock_external_median_ns
            if aggregate.stock_external_median_ns
            else 0.0
        )
        fraction = (
            aggregate.array_envelope_median_ns
            / aggregate.instrumented_internal_median_ns
            if aggregate.instrumented_internal_median_ns
            else 0.0
        )
        lines = [
            f"comparison: {self.repetitions} repetitions after {self.warmups} warmups",
            "stock_external and instrumented_external are pipe round trips; instrumented_internal and array share the Z3 check boundary",
            (
                f"aggregate: checks={aggregate.check_count} depths={aggregate.depth_count} "
                f"stock_external={aggregate.stock_external_median_ns / 1_000_000:.3f}ms "
                f"instrumented_external={aggregate.instrumented_external_median_ns / 1_000_000:.3f}ms "
                f"external_overhead={overhead:+.1%} "
                f"instrumented_internal={aggregate.instrumented_internal_median_ns / 1_000_000:.3f}ms "
                f"array={aggregate.array_envelope_median_ns / 1_000_000:.3f}ms "
                f"array_fraction={fraction:.1%}"
            ),
            "depths:",
        ]
        for depth in self.depths:
            fraction = (
                depth.array_envelope_median_ns
                / depth.instrumented_internal_median_ns
                if depth.instrumented_internal_median_ns
                else 0.0
            )
            lines.append(
                f"  {depth.depth}: check_ids={','.join(map(str, depth.check_ids))} "
                f"stock_external={depth.stock_external_median_ns / 1_000_000:.3f}ms "
                f"instrumented_external={depth.instrumented_external_median_ns / 1_000_000:.3f}ms "
                f"instrumented_internal={depth.instrumented_internal_median_ns / 1_000_000:.3f}ms "
                f"array={depth.array_envelope_median_ns / 1_000_000:.3f}ms "
                f"array_fraction={fraction:.1%}"
            )
        return "\n".join(lines)


def compare_capture(
    capture_dir: Path,
    builder_manifest: dict[str, Any],
    *,
    warmups: int = 3,
    repetitions: int = 15,
    timeout_seconds: float = 60.0,
) -> ComparisonReport:
    """Measure paired replays and align their check records."""

    if warmups < 0:
        raise ReplayError("warmups must be nonnegative")
    if repetitions <= 0:
        raise ReplayError("repetitions must be positive")
    if timeout_seconds <= 0:
        raise ReplayError("timeout must be positive")
    capture_dir = capture_dir.expanduser().resolve()
    transcript, indexed_checks = _load_capture(capture_dir)
    profile_checks = _load_profile_checks(capture_dir, indexed_checks)
    stock_binary = _builder_binaries(builder_manifest)["stock"]

    for _ in range(warmups):
        _run_repetition(
            transcript, indexed_checks, stock_binary, timeout_seconds
        )
        profile_instrumented_replay(
            capture_dir, builder_manifest, timeout_seconds=timeout_seconds
        )

    stock_samples = []
    instrumented = []
    for repetition in range(repetitions):
        if repetition % 2 == 0:
            stock_sample = _run_repetition(
                transcript, indexed_checks, stock_binary, timeout_seconds
            )
            instrumented_run = profile_instrumented_replay(
                capture_dir, builder_manifest, timeout_seconds=timeout_seconds
            )
        else:
            instrumented_run = profile_instrumented_replay(
                capture_dir, builder_manifest, timeout_seconds=timeout_seconds
            )
            stock_sample = _run_repetition(
                transcript, indexed_checks, stock_binary, timeout_seconds
            )
        stock_samples.append(stock_sample)
        instrumented.append(instrumented_run)

    stock = aggregate_stock_timings(
        capture_dir,
        stock_binary,
        warmups,
        repetitions,
        indexed_checks,
        profile_checks,
        tuple(stock_samples),
    )
    return _join(stock, tuple(instrumented))


def write_comparison_report(path: Path, report: ComparisonReport) -> None:
    path = path.expanduser()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report.to_dict(), indent=2, sort_keys=True) + "\n")


def _join(
    stock: TimingReport, instrumented: tuple[InstrumentedReplay, ...]
) -> ComparisonReport:
    if len(instrumented) != stock.repetitions:
        raise ReplayError("instrumented repetition count does not match stock")
    if any(len(run.checks) != len(stock.checks) for run in instrumented):
        raise ReplayError("instrumented check count does not match stock")
    for run in instrumented:
        for stock_check, instrumented_check in zip(stock.checks, run.checks):
            if (
                instrumented_check.check_id != stock_check.check_id
                or instrumented_check.result != stock_check.result
            ):
                raise ReplayError(
                    f"instrumented check {instrumented_check.check_id} "
                    "does not match stock timing"
                )

    checks = []
    for index, stock_check in enumerate(stock.checks):
        instrumented_external_samples = tuple(
            run.checks[index].external_elapsed_ns for run in instrumented
        )
        instrumented_samples = tuple(
            run.checks[index].check_elapsed_ns for run in instrumented
        )
        envelope_samples = tuple(
            run.checks[index].array_envelope_ns for run in instrumented
        )
        residual_samples = tuple(
            elapsed - envelope
            for elapsed, envelope in zip(instrumented_samples, envelope_samples)
        )
        instrumented_external_median, instrumented_external_mad = (
            _median_and_mad(instrumented_external_samples)
        )
        instrumented_median, instrumented_mad = _median_and_mad(
            instrumented_samples
        )
        envelope_median, envelope_mad = _median_and_mad(envelope_samples)
        residual_median, residual_mad = _median_and_mad(residual_samples)
        checks.append(
            CheckComparison(
                check_id=stock_check.check_id,
                depth=stock_check.depth,
                refinement_id=stock_check.refinement_id,
                refinement_step=stock_check.refinement_step,
                result=stock_check.result,
                instances_total=stock_check.instances_total,
                instances_added_since_previous_check=(
                    stock_check.instances_added_since_previous_check
                ),
                stock_external_samples_ns=stock_check.samples_ns,
                stock_external_median_ns=stock_check.median_ns,
                stock_external_mad_ns=stock_check.mad_ns,
                instrumented_external_samples_ns=instrumented_external_samples,
                instrumented_external_median_ns=instrumented_external_median,
                instrumented_external_mad_ns=instrumented_external_mad,
                instrumented_internal_samples_ns=instrumented_samples,
                instrumented_internal_median_ns=instrumented_median,
                instrumented_internal_mad_ns=instrumented_mad,
                array_envelope_samples_ns=envelope_samples,
                array_envelope_median_ns=envelope_median,
                array_envelope_mad_ns=envelope_mad,
                non_array_residual_samples_ns=residual_samples,
                non_array_residual_median_ns=residual_median,
                non_array_residual_mad_ns=residual_mad,
            )
        )

    depths = []
    check_by_id = {check.check_id: check for check in checks}
    for stock_depth in stock.depths:
        depth_checks = tuple(check_by_id[check_id] for check_id in stock_depth.check_ids)
        instrumented_external_samples = tuple(
            sum(
                run.checks[check_id].external_elapsed_ns
                for check_id in stock_depth.check_ids
            )
            for run in instrumented
        )
        instrumented_samples = tuple(
            sum(run.checks[check_id].check_elapsed_ns for check_id in stock_depth.check_ids)
            for run in instrumented
        )
        envelope_samples = tuple(
            sum(run.checks[check_id].array_envelope_ns for check_id in stock_depth.check_ids)
            for run in instrumented
        )
        residual_samples = tuple(
            elapsed - envelope
            for elapsed, envelope in zip(instrumented_samples, envelope_samples)
        )
        instrumented_external_median, instrumented_external_mad = (
            _median_and_mad(instrumented_external_samples)
        )
        instrumented_median, instrumented_mad = _median_and_mad(
            instrumented_samples
        )
        envelope_median, envelope_mad = _median_and_mad(envelope_samples)
        residual_median, residual_mad = _median_and_mad(residual_samples)
        depths.append(
            DepthComparison(
                depth=stock_depth.depth,
                check_ids=stock_depth.check_ids,
                results=stock_depth.results,
                stock_external_samples_ns=stock_depth.samples_ns,
                stock_external_median_ns=stock_depth.median_ns,
                stock_external_mad_ns=stock_depth.mad_ns,
                instrumented_external_samples_ns=instrumented_external_samples,
                instrumented_external_median_ns=instrumented_external_median,
                instrumented_external_mad_ns=instrumented_external_mad,
                instrumented_internal_samples_ns=instrumented_samples,
                instrumented_internal_median_ns=instrumented_median,
                instrumented_internal_mad_ns=instrumented_mad,
                array_envelope_samples_ns=envelope_samples,
                array_envelope_median_ns=envelope_median,
                array_envelope_mad_ns=envelope_mad,
                non_array_residual_samples_ns=residual_samples,
                non_array_residual_median_ns=residual_median,
                non_array_residual_mad_ns=residual_mad,
            )
        )
        if tuple(check.result for check in depth_checks) != stock_depth.results:
            raise ReplayError(
                f"comparison depth {stock_depth.depth} results are misaligned"
            )

    return ComparisonReport(
        capture_dir=stock.capture_dir,
        stock_binary=stock.stock_binary,
        instrumented_binary=instrumented[0].binary,
        warmups=stock.warmups,
        repetitions=stock.repetitions,
        aggregate=_aggregate(tuple(checks), len(depths), stock.repetitions),
        checks=tuple(checks),
        depths=tuple(depths),
    )


def _aggregate(
    checks: tuple[CheckComparison, ...], depth_count: int, repetitions: int
) -> AggregateComparison:
    def samples(field: str) -> tuple[int, ...]:
        return tuple(
            sum(getattr(check, field)[repetition] for check in checks)
            for repetition in range(repetitions)
        )

    stock_external = samples("stock_external_samples_ns")
    instrumented_external = samples("instrumented_external_samples_ns")
    external_overhead = tuple(
        instrumented - stock
        for stock, instrumented in zip(stock_external, instrumented_external)
    )
    instrumented_internal = samples("instrumented_internal_samples_ns")
    array_envelope = samples("array_envelope_samples_ns")
    non_array_residual = samples("non_array_residual_samples_ns")
    stock_external_median, stock_external_mad = _median_and_mad(stock_external)
    instrumented_external_median, instrumented_external_mad = _median_and_mad(
        instrumented_external
    )
    external_overhead_median, external_overhead_mad = _median_and_mad(
        external_overhead
    )
    instrumented_internal_median, instrumented_internal_mad = _median_and_mad(
        instrumented_internal
    )
    array_envelope_median, array_envelope_mad = _median_and_mad(array_envelope)
    non_array_residual_median, non_array_residual_mad = _median_and_mad(
        non_array_residual
    )
    return AggregateComparison(
        check_count=len(checks),
        depth_count=depth_count,
        stock_external_samples_ns=stock_external,
        stock_external_median_ns=stock_external_median,
        stock_external_mad_ns=stock_external_mad,
        instrumented_external_samples_ns=instrumented_external,
        instrumented_external_median_ns=instrumented_external_median,
        instrumented_external_mad_ns=instrumented_external_mad,
        external_overhead_samples_ns=external_overhead,
        external_overhead_median_ns=external_overhead_median,
        external_overhead_mad_ns=external_overhead_mad,
        instrumented_internal_samples_ns=instrumented_internal,
        instrumented_internal_median_ns=instrumented_internal_median,
        instrumented_internal_mad_ns=instrumented_internal_mad,
        array_envelope_samples_ns=array_envelope,
        array_envelope_median_ns=array_envelope_median,
        array_envelope_mad_ns=array_envelope_mad,
        non_array_residual_samples_ns=non_array_residual,
        non_array_residual_median_ns=non_array_residual_median,
        non_array_residual_mad_ns=non_array_residual_mad,
    )
