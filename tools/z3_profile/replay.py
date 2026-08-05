"""Replay one Yardbird capture through the Z3 pair built by z3-builder."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .runner import (
    BuilderBinaries,
    LoadedCapture,
    ReplayRunner,
    read_json_object,
)


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


def replay_build_pair(
    capture_dir: Path,
    builder_manifest: dict[str, Any],
    *,
    timeout_seconds: float = 60.0,
) -> PairReplay:
    """Replay a capture once through both binaries named by z3-builder."""

    capture = LoadedCapture.load(capture_dir)
    binaries = BuilderBinaries.from_manifest(builder_manifest)
    stock_run = ReplayRunner(
        binaries.stock, label="stock", timeout_seconds=timeout_seconds
    ).run(capture)
    instrumented_run = ReplayRunner(
        binaries.instrumented,
        label="instrumented",
        timeout_seconds=timeout_seconds,
    ).run(capture)
    return PairReplay(
        capture.expected_results,
        SolverReplay("stock", binaries.stock, stock_run.results),
        SolverReplay("instrumented", binaries.instrumented, instrumented_run.results),
    )


def load_builder_manifest(build_dir: Path) -> dict[str, Any]:
    """Load an existing z3-builder output directory."""

    return read_json_object(
        build_dir.expanduser().resolve() / "manifest.json", "z3-builder manifest"
    )
