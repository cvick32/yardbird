"""Bug mutators derived from correct semantic programs."""

from __future__ import annotations

from .families import (
    build_dual_counter_copy,
    build_single_loop_copy,
    build_single_loop_init,
    build_single_loop_transform,
    build_two_phase_transform,
)
from .ir import BenchmarkSpec, BugKind


def apply_bug_mutation(spec: BenchmarkSpec, bug_kind: BugKind) -> BenchmarkSpec:
    if bug_kind != BugKind.WRONG_WRITE_INDEX:
        raise NotImplementedError(f"unsupported bug kind: {bug_kind.value}")
    ordinal = _extract_ordinal(spec)

    if spec.family_name.value == "copy" and spec.skeleton_type.value == "single_loop":
        return build_single_loop_copy(seed=spec.seed, ordinal=ordinal, bug_flag=True)
    if spec.family_name.value == "init" and spec.skeleton_type.value == "single_loop":
        return build_single_loop_init(seed=spec.seed, ordinal=ordinal, bug_flag=True)
    if spec.family_name.value == "transform" and spec.skeleton_type.value == "single_loop":
        return build_single_loop_transform(seed=spec.seed, ordinal=ordinal, bug_flag=True)
    if spec.family_name.value == "copy" and spec.skeleton_type.value == "dual_counter":
        return build_dual_counter_copy(seed=spec.seed, ordinal=ordinal, bug_flag=True)
    if spec.family_name.value == "transform" and spec.skeleton_type.value == "two_phase":
        return build_two_phase_transform(seed=spec.seed, ordinal=ordinal, bug_flag=True)

    raise NotImplementedError(
        "wrong_write_index is not implemented for "
        f"{spec.family_name.value}/{spec.skeleton_type.value}"
    )


def _extract_ordinal(spec: BenchmarkSpec) -> int:
    token = spec.benchmark_name.split("_")[-2]
    return int(token)
