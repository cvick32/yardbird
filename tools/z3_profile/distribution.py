"""Shared timing distribution used at every comparison level."""

from __future__ import annotations

import statistics
from dataclasses import dataclass


@dataclass(frozen=True)
class TimingDistribution:
    samples_ns: tuple[int, ...]
    median_ns: int
    mad_ns: int

    @classmethod
    def from_samples(cls, samples: tuple[int, ...]) -> TimingDistribution:
        if not samples:
            raise ValueError("a timing distribution requires at least one sample")
        median = int(statistics.median(samples))
        mad = int(statistics.median(abs(sample - median) for sample in samples))
        return cls(samples, median, mad)
