"""Configuration objects for benchmark synthesis."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class YardbirdRunConfig:
    strategy: str
    depth: int
    cost_function: str | None = None
    timeout_seconds: int = 10
