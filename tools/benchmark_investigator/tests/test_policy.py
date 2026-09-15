import asyncio

import pytest
from pydantic import ValidationError

from benchmark_investigator.models import (
    ACTION_ADAPTER,
    ConfigPatch,
    ExperimentConfig,
    resolve_patch,
)
from benchmark_investigator.scheduler import Scheduler


def test_patch_compares_actual_changes_and_rejects_four_knobs():
    baseline = ExperimentConfig()
    allowed = resolve_patch(
        baseline,
        ConfigPatch(
            cost_function="ast-size",
            egraph_builder="full",
            candidate_winners_per_group=1,
            instantiation_ranker="prefer-source",
        ),
        False,
    )
    assert allowed.strategy == "abstract"
    with pytest.raises(ValueError, match="three"):
        resolve_patch(
            baseline,
            ConfigPatch(
                cost_function="ast-size",
                egraph_builder="full",
                candidate_winners_per_group=1,
                instantiation_ranker="term-cost",
            ),
            False,
        )
    with pytest.raises(ValueError, match="ranker model"):
        resolve_patch(baseline, ConfigPatch(cost_function="logistic-regression"), False)
    with pytest.raises(ValueError, match="abstract"):
        resolve_patch(ExperimentConfig(strategy="concrete"), ConfigPatch(), False)
    with pytest.raises(ValidationError):
        ConfigPatch.model_validate({"strategy": "concrete"})
    with pytest.raises(ValidationError):
        ConfigPatch(candidate_winners_per_group=3)
    with pytest.raises(ValidationError):
        ConfigPatch(candidate_winners_per_group=True)


def test_actions_reject_unknown_fields_and_invalid_read_ranges():
    with pytest.raises(ValidationError):
        ACTION_ADAPTER.validate_python({"action": "FINISH", "rationale": "done", "shell": "whoami"})
    with pytest.raises(ValidationError):
        ACTION_ADAPTER.validate_python(
            {
                "action": "INSPECT_SOURCE",
                "mode": "read",
                "reason": "inspect",
                "path": "src/lib.rs",
                "start_line": 1,
                "end_line": 300,
            }
        )


def test_scheduler_caps_parallelism_and_serializes_each_benchmark():
    async def scenario():
        scheduler = Scheduler(2)
        active, maximum = 0, 0
        per_benchmark = set()

        async def run(bid):
            async def operation():
                nonlocal active, maximum
                assert bid not in per_benchmark
                per_benchmark.add(bid)
                active += 1
                maximum = max(maximum, active)
                await asyncio.sleep(0.01)
                active -= 1
                per_benchmark.remove(bid)

            await scheduler.run(bid, operation)

        await asyncio.gather(*(run(bid) for bid in ["a", "a", "b", "c", "b"]))
        assert maximum == 2

    asyncio.run(scenario())
