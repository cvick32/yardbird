"""Corpus manifests and run manifests."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import json
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class CorpusEntry:
    benchmark_name: str
    benchmark_path: str
    metadata_path: str
    bug_flag: bool


@dataclass(frozen=True)
class RejectionEntry:
    benchmark_name: str
    reason: str


@dataclass(frozen=True)
class CorpusManifest:
    corpus_name: str
    seed: int
    entries: list[CorpusEntry]
    rejections: list[RejectionEntry]

    def to_dict(self) -> dict[str, Any]:
        return {
            "corpus_name": self.corpus_name,
            "seed": self.seed,
            "entries": [asdict(entry) for entry in self.entries],
            "rejections": [asdict(entry) for entry in self.rejections],
        }

    def write_json(self, path: Path) -> None:
        path.write_text(json.dumps(self.to_dict(), indent=2, sort_keys=True) + "\n")


@dataclass(frozen=True)
class RunEntry:
    benchmark_name: str
    benchmark_path: str
    strategy: str
    cost_function: str | None
    depth: int
    duration_seconds: float
    exit_code: int
    status: str


def write_run_manifest(path: Path, entries: list[RunEntry]) -> None:
    payload = {"entries": [asdict(entry) for entry in entries]}
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
