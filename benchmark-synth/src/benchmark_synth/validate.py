"""Structural validation helpers."""

from __future__ import annotations

import hashlib

from .ir import BenchmarkSpec, validate_benchmark_spec
from .lower_vmt import lower_benchmark


def normalized_vmt_hash(spec: BenchmarkSpec) -> str:
    lowered = lower_benchmark(spec)
    normalized = "\n".join(line.strip() for line in lowered.vmt_text.splitlines() if line.strip())
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def validate_structural(spec: BenchmarkSpec) -> None:
    validate_benchmark_spec(spec)
    lowered = lower_benchmark(spec)
    if "(let " in lowered.vmt_text:
        raise ValueError("lowered VMT must not contain let bindings")
