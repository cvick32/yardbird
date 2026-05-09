"""Deterministic benchmark naming helpers."""

from __future__ import annotations


def benchmark_name(
    *,
    family: str,
    skeleton: str,
    property_family: str,
    seed: int,
    ordinal: int,
    bug_flag: bool,
) -> str:
    bug_suffix = "buggy" if bug_flag else "safe"
    return (
        f"{family}_{skeleton}_{property_family}_seed{seed:04d}_"
        f"{ordinal:04d}_{bug_suffix}"
    )


def metadata_filename(benchmark_name_value: str) -> str:
    return f"{benchmark_name_value}.json"


def benchmark_filename(benchmark_name_value: str) -> str:
    return f"{benchmark_name_value}.vmt"
