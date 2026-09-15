"""Bounded execution pool, with one serial experiment stream per benchmark."""

import asyncio
from collections import defaultdict


class Scheduler:
    def __init__(self, parallel_runs: int):
        self.slots = asyncio.Semaphore(parallel_runs)
        self.benchmarks = defaultdict(asyncio.Lock)

    async def run(self, benchmark_id, operation):
        async with self.benchmarks[benchmark_id], self.slots:
            return await operation()
