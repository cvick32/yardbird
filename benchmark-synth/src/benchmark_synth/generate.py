"""Corpus generation."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import random

from .families import FamilyBuilder, supported_structures
from .ir import BenchmarkSpec, FamilyName, PropertyFamily, SkeletonType
from .lower_vmt import lower_benchmark
from .manifests import CorpusEntry, CorpusManifest, RejectionEntry
from .mutators import apply_bug_mutation
from .naming import benchmark_filename, metadata_filename
from .validate import validate_structural


@dataclass(frozen=True)
class GenerateConfig:
    output_dir: Path
    seed: int
    count: int
    family: FamilyName | None = None
    skeleton: SkeletonType | None = None
    property_family: PropertyFamily | None = None
    bug_ratio: float = 0.0


def generate_corpus(config: GenerateConfig) -> CorpusManifest:
    structures = _matching_structures(config)
    if not structures:
        raise ValueError("no supported structures match the requested filters")

    benchmark_dir = config.output_dir / "benchmarks"
    metadata_dir = config.output_dir / "metadata"
    benchmark_dir.mkdir(parents=True, exist_ok=True)
    metadata_dir.mkdir(parents=True, exist_ok=True)

    rng = random.Random(config.seed)
    entries: list[CorpusEntry] = []
    rejections: list[RejectionEntry] = []

    for ordinal in range(config.count):
        try:
            bug_flag = rng.random() < config.bug_ratio
            builder = rng.choice(structures)
            spec = _build_spec(builder, config.seed, ordinal, bug_flag)
            validate_structural(spec)
            lowered = lower_benchmark(spec)
            metadata = spec.metadata()

            bench_path = benchmark_dir / benchmark_filename(spec.benchmark_name)
            meta_path = metadata_dir / metadata_filename(spec.benchmark_name)
            bench_path.write_text(lowered.vmt_text)
            metadata.write_json(meta_path)

            entries.append(
                CorpusEntry(
                    benchmark_name=spec.benchmark_name,
                    benchmark_path=str(bench_path),
                    metadata_path=str(meta_path),
                    bug_flag=spec.bug_flag,
                )
            )
        except Exception as exc:  # pragma: no cover - defensive bookkeeping
            rejections.append(
                RejectionEntry(
                    benchmark_name=f"rejected_seed{config.seed}_{ordinal:04d}",
                    reason=str(exc),
                )
            )

    manifest = CorpusManifest(
        corpus_name=config.output_dir.name,
        seed=config.seed,
        entries=entries,
        rejections=rejections,
    )
    manifest.write_json(config.output_dir / "manifest.json")
    return manifest


def _matching_structures(config: GenerateConfig) -> list[FamilyBuilder]:
    matches: list[FamilyBuilder] = []
    for (family, skeleton, property_family), builder in supported_structures().items():
        if config.family is not None and family != config.family:
            continue
        if config.skeleton is not None and skeleton != config.skeleton:
            continue
        if (
            config.property_family is not None
            and property_family != config.property_family
        ):
            continue
        matches.append(builder)
    return matches


def _build_spec(
    builder: FamilyBuilder, seed: int, ordinal: int, bug_flag: bool
) -> BenchmarkSpec:
    spec = builder(seed=seed, ordinal=ordinal, bug_flag=False)
    if bug_flag:
        spec = apply_bug_mutation(spec, bug_kind=spec_bug_kind())
    return spec


def spec_bug_kind():
    from .ir import BugKind

    return BugKind.WRONG_WRITE_INDEX
