"""Bug mutators derived from correct semantic programs."""

from __future__ import annotations

from dataclasses import replace

from .families import build_single_loop_copy
from .ir import BenchmarkSpec, BugKind


def apply_bug_mutation(spec: BenchmarkSpec, bug_kind: BugKind) -> BenchmarkSpec:
    if bug_kind != BugKind.WRONG_WRITE_INDEX:
        raise NotImplementedError(f"unsupported bug kind: {bug_kind.value}")
    if spec.family_name.value != "copy" or spec.skeleton_type.value != "single_loop":
        raise NotImplementedError("wrong_write_index is only implemented for single_loop copy")
    return build_single_loop_copy(seed=spec.seed, ordinal=_extract_ordinal(spec), bug_flag=True)


def _extract_ordinal(spec: BenchmarkSpec) -> int:
    token = spec.benchmark_name.split("_")[-2]
    return int(token)
