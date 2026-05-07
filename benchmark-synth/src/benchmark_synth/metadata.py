"""Coarse benchmark metadata."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any


ALLOWED_METADATA_FIELDS = {
    "family_name",
    "skeleton_type",
    "property_family",
    "bug_flag",
    "estimated_difficulty",
    "generator_version",
    "seed",
    "benchmark_name",
}


@dataclass(frozen=True)
class BenchmarkMetadata:
    family_name: str
    skeleton_type: str
    property_family: str
    bug_flag: bool
    estimated_difficulty: str
    generator_version: str
    seed: int
    benchmark_name: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "family_name": self.family_name,
            "skeleton_type": self.skeleton_type,
            "property_family": self.property_family,
            "bug_flag": self.bug_flag,
            "estimated_difficulty": self.estimated_difficulty,
            "generator_version": self.generator_version,
            "seed": self.seed,
            "benchmark_name": self.benchmark_name,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "BenchmarkMetadata":
        unknown = set(data) - ALLOWED_METADATA_FIELDS
        if unknown:
            raise ValueError(f"unexpected metadata fields: {sorted(unknown)}")
        return cls(**data)

    def write_json(self, path: Path) -> None:
        path.write_text(json.dumps(self.to_dict(), indent=2, sort_keys=True) + "\n")
