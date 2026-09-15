import asyncio
import json

import pytest

from benchmark_investigator.agent import MockBackend, run_campaign
from benchmark_investigator.campaign import Campaign, create_campaign
from benchmark_investigator.models import CampaignConfig, ConfigPatch, RunAction


def action(parent, **patch):
    return RunAction(
        parent_run_id=parent,
        config_patch=ConfigPatch(**patch),
        hypothesis="test",
        expected_signal="test",
        rationale="test",
    )


@pytest.mark.parametrize("budget", [10, 15])
def test_campaign_uses_budget_and_resumes_without_repeating(
    fake_binary, source_root, tmp_path, budget
):
    campaign = create_campaign(
        source_root,
        tmp_path / "campaign",
        CampaignConfig(benchmarks=["one.vmt", "two.vmt"], executions_per_benchmark=budget),
        fake_binary,
    )
    with campaign.lock():
        asyncio.run(run_campaign(campaign, MockBackend()))
    for bid in campaign.benchmarks:
        rows = campaign.runs(bid)
        assert len(rows) == budget
        assert json.loads(rows[0]["config_json"])["strategy"] == "abstract"
        assert json.loads(rows[1]["config_json"])["strategy"] == "concrete"
        assert all(r["parent_run_id"] == rows[0]["run_id"] for r in rows[2:])
        assert all(r["summary_path"] for r in rows)
        assert (campaign.directory / "FINDINGS" / f"FINDINGS-{bid}.md").exists()
    resumed = Campaign(campaign.directory)
    with resumed.lock():
        asyncio.run(run_campaign(resumed, MockBackend()))
    assert all(len(resumed.runs(bid)) == budget for bid in resumed.benchmarks)
    assert resumed.context(bid)["runs_remaining"] == 0
    with pytest.raises(ValueError, match="budget exhausted"):
        asyncio.run(resumed.run(bid, action(rows[0]["run_id"])))


def test_budget_lineage_and_pin_validation(fake_binary, source_root, tmp_path):
    campaign = create_campaign(
        source_root,
        tmp_path / "campaign",
        CampaignConfig(benchmarks=["one.vmt", "two.vmt"]),
        fake_binary,
    )
    first, second = list(campaign.benchmarks)

    async def scenario():
        await run_campaign(campaign, MockBackend(), baseline_only=True)
        with pytest.raises(ValueError, match="Parent"):
            await campaign.run(first, action(campaign.runs(second)[0]["run_id"]))
        with pytest.raises(ValueError, match="abstract"):
            await campaign.run(first, action(campaign.runs(first)[1]["run_id"]))
        assert len(campaign.runs(first)) == 2

    asyncio.run(scenario())
    (source_root / "src/lib.rs").write_text("changed")
    with pytest.raises(ValueError, match="source changed"):
        campaign.verify_pins()


def test_source_access_rejects_traversal_and_symlinks(fake_binary, source_root, tmp_path):
    campaign = create_campaign(
        source_root, tmp_path / "campaign", CampaignConfig(benchmarks=["one.vmt"]), fake_binary
    )
    assert campaign.source.search("strategy_sat")["matches"][0]["line"] == 1
    assert "hello" in campaign.source.read("src/lib.rs", 1, 2)["text"]
    with pytest.raises(ValueError, match="escapes"):
        campaign.source.read("../outside", 1, 2)
    (source_root / "src/lib.rs").unlink()
    (source_root / "src/lib.rs").symlink_to(tmp_path / "outside")
    with pytest.raises(ValueError, match="escapes"):
        campaign.source.read("src/lib.rs", 1, 2)


def test_rejected_agent_action_does_not_consume_a_run(fake_binary, source_root, tmp_path):
    class EarlyFinish(MockBackend):
        calls = 0

        async def decide(self, context, directory):
            from benchmark_investigator.models import FinishAction

            self.calls += 1
            if self.calls == 1:
                return FinishAction(rationale="too early")
            return await super().decide(context, directory)

    campaign = create_campaign(
        source_root, tmp_path / "campaign", CampaignConfig(benchmarks=["one.vmt"]), fake_binary
    )
    backend = EarlyFinish()
    asyncio.run(run_campaign(campaign, backend))
    bid = next(iter(campaign.benchmarks))
    assert len(campaign.runs(bid)) == 10
    assert backend.calls == 10
    assert (
        '"kind": "rejected"'
        in (campaign.directory / "benchmarks" / bid / "agent-events.jsonl").read_text()
    )
