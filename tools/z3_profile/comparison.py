"""Join stock replay timings with instrumented-Z3 array summaries."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from .distribution import TimingDistribution
from .instrumented import InstrumentedReplay, profile_instrumented_replay
from .runner import BuilderBinaries, LoadedCapture, ReplayError, ReplayRunner
from .timing import TimingReport, aggregate_stock_timings


@dataclass(frozen=True)
class CheckComparison:
    check_id: int
    depth: int
    refinement_id: int
    refinement_step: int
    result: str
    instances_total: int
    instances_added_since_previous_check: int
    stock_external: TimingDistribution
    instrumented_external: TimingDistribution
    instrumented_internal: TimingDistribution
    array_envelope: TimingDistribution
    non_array_residual: TimingDistribution


@dataclass(frozen=True)
class DepthComparison:
    depth: int
    check_ids: tuple[int, ...]
    refinement_ids: tuple[int, ...]
    refinement_steps: tuple[int, ...]
    results: tuple[str, ...]
    instances_total: int
    instances_added: int
    stock_external: TimingDistribution
    instrumented_external: TimingDistribution
    instrumented_internal: TimingDistribution
    array_envelope: TimingDistribution
    non_array_residual: TimingDistribution


@dataclass(frozen=True)
class AggregateComparison:
    check_count: int
    depth_count: int
    stock_external: TimingDistribution
    instrumented_external: TimingDistribution
    external_overhead: TimingDistribution
    instrumented_internal: TimingDistribution
    array_envelope: TimingDistribution
    non_array_residual: TimingDistribution


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
            aggregate.external_overhead.median_ns / aggregate.stock_external.median_ns
            if aggregate.stock_external.median_ns
            else 0.0
        )
        fraction = (
            aggregate.array_envelope.median_ns
            / aggregate.instrumented_internal.median_ns
            if aggregate.instrumented_internal.median_ns
            else 0.0
        )
        lines = [
            f"comparison: {self.repetitions} repetitions after {self.warmups} warmups",
            "stock_external and instrumented_external are pipe round trips; instrumented_internal and array share the Z3 check boundary",
            (
                f"aggregate: checks={aggregate.check_count} depths={aggregate.depth_count} "
                f"stock_external={aggregate.stock_external.median_ns / 1_000_000:.3f}ms "
                f"instrumented_external={aggregate.instrumented_external.median_ns / 1_000_000:.3f}ms "
                f"external_overhead={overhead:+.1%} "
                f"instrumented_internal={aggregate.instrumented_internal.median_ns / 1_000_000:.3f}ms "
                f"array={aggregate.array_envelope.median_ns / 1_000_000:.3f}ms "
                f"array_fraction={fraction:.1%}"
            ),
            "depths:",
        ]
        for depth in self.depths:
            fraction = (
                depth.array_envelope.median_ns / depth.instrumented_internal.median_ns
                if depth.instrumented_internal.median_ns
                else 0.0
            )
            lines.append(
                f"  {depth.depth}: check_ids={','.join(map(str, depth.check_ids))} "
                f"refinements={','.join(map(str, depth.refinement_ids))} "
                f"instances={depth.instances_total} (+{depth.instances_added}) "
                f"stock_external={depth.stock_external.median_ns / 1_000_000:.3f}ms "
                f"instrumented_external={depth.instrumented_external.median_ns / 1_000_000:.3f}ms "
                f"instrumented_internal={depth.instrumented_internal.median_ns / 1_000_000:.3f}ms "
                f"array={depth.array_envelope.median_ns / 1_000_000:.3f}ms "
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

    capture = LoadedCapture.load(capture_dir)
    profile_checks = capture.load_profile_checks()
    stock_binary = BuilderBinaries.from_manifest(builder_manifest).stock
    stock_runner = ReplayRunner(
        stock_binary, label="stock", timeout_seconds=timeout_seconds
    )

    for _ in range(warmups):
        stock_runner.run(capture)
        profile_instrumented_replay(
            capture.directory,
            builder_manifest,
            timeout_seconds=timeout_seconds,
        )

    stock_samples = []
    instrumented = []
    for repetition in range(repetitions):
        if repetition % 2 == 0:
            stock_run = stock_runner.run(capture)
            instrumented_run = profile_instrumented_replay(
                capture.directory,
                builder_manifest,
                timeout_seconds=timeout_seconds,
            )
        else:
            instrumented_run = profile_instrumented_replay(
                capture.directory,
                builder_manifest,
                timeout_seconds=timeout_seconds,
            )
            stock_run = stock_runner.run(capture)
        stock_samples.append(stock_run.timings_ns)
        instrumented.append(instrumented_run)

    stock = aggregate_stock_timings(
        capture,
        stock_binary,
        warmups,
        repetitions,
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

    checks = tuple(
        _join_check(index, stock_check, instrumented)
        for index, stock_check in enumerate(stock.checks)
    )
    check_by_id = {check.check_id: check for check in checks}
    depths = tuple(
        _join_depth(stock_depth, check_by_id, instrumented)
        for stock_depth in stock.depths
    )
    return ComparisonReport(
        capture_dir=stock.capture_dir,
        stock_binary=stock.stock_binary,
        instrumented_binary=instrumented[0].binary,
        warmups=stock.warmups,
        repetitions=stock.repetitions,
        aggregate=_aggregate(checks, len(depths), stock.repetitions),
        checks=checks,
        depths=depths,
    )


def _join_check(index, stock_check, instrumented) -> CheckComparison:
    instrumented_external = tuple(
        run.checks[index].external_elapsed_ns for run in instrumented
    )
    instrumented_internal = tuple(
        run.checks[index].check_elapsed_ns for run in instrumented
    )
    array_envelope = tuple(run.checks[index].array_envelope_ns for run in instrumented)
    residual = tuple(
        elapsed - envelope
        for elapsed, envelope in zip(instrumented_internal, array_envelope)
    )
    return CheckComparison(
        check_id=stock_check.check_id,
        depth=stock_check.depth,
        refinement_id=stock_check.refinement_id,
        refinement_step=stock_check.refinement_step,
        result=stock_check.result,
        instances_total=stock_check.instances_total,
        instances_added_since_previous_check=(
            stock_check.instances_added_since_previous_check
        ),
        stock_external=stock_check.timing,
        instrumented_external=TimingDistribution.from_samples(instrumented_external),
        instrumented_internal=TimingDistribution.from_samples(instrumented_internal),
        array_envelope=TimingDistribution.from_samples(array_envelope),
        non_array_residual=TimingDistribution.from_samples(residual),
    )


def _join_depth(stock_depth, check_by_id, instrumented) -> DepthComparison:
    depth_checks = tuple(check_by_id[check_id] for check_id in stock_depth.check_ids)

    def summed(field: str) -> tuple[int, ...]:
        return tuple(
            sum(
                getattr(run.checks[check_id], field)
                for check_id in stock_depth.check_ids
            )
            for run in instrumented
        )

    instrumented_external = summed("external_elapsed_ns")
    instrumented_internal = summed("check_elapsed_ns")
    array_envelope = summed("array_envelope_ns")
    residual = tuple(
        elapsed - envelope
        for elapsed, envelope in zip(instrumented_internal, array_envelope)
    )
    if tuple(check.result for check in depth_checks) != stock_depth.results:
        raise ReplayError(
            f"comparison depth {stock_depth.depth} results are misaligned"
        )
    return DepthComparison(
        depth=stock_depth.depth,
        check_ids=stock_depth.check_ids,
        refinement_ids=stock_depth.refinement_ids,
        refinement_steps=stock_depth.refinement_steps,
        results=stock_depth.results,
        instances_total=stock_depth.instances_total,
        instances_added=stock_depth.instances_added,
        stock_external=stock_depth.timing,
        instrumented_external=TimingDistribution.from_samples(instrumented_external),
        instrumented_internal=TimingDistribution.from_samples(instrumented_internal),
        array_envelope=TimingDistribution.from_samples(array_envelope),
        non_array_residual=TimingDistribution.from_samples(residual),
    )


def _aggregate(
    checks: tuple[CheckComparison, ...], depth_count: int, repetitions: int
) -> AggregateComparison:
    def samples(field: str) -> tuple[int, ...]:
        return tuple(
            sum(getattr(check, field).samples_ns[repetition] for check in checks)
            for repetition in range(repetitions)
        )

    stock_external = samples("stock_external")
    instrumented_external = samples("instrumented_external")
    external_overhead = tuple(
        instrumented - stock
        for stock, instrumented in zip(stock_external, instrumented_external)
    )
    return AggregateComparison(
        check_count=len(checks),
        depth_count=depth_count,
        stock_external=TimingDistribution.from_samples(stock_external),
        instrumented_external=TimingDistribution.from_samples(instrumented_external),
        external_overhead=TimingDistribution.from_samples(external_overhead),
        instrumented_internal=TimingDistribution.from_samples(
            samples("instrumented_internal")
        ),
        array_envelope=TimingDistribution.from_samples(samples("array_envelope")),
        non_array_residual=TimingDistribution.from_samples(
            samples("non_array_residual")
        ),
    )
