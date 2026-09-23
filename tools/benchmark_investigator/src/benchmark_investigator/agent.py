"""Campaign-driven logical agents. No model invocation stays alive during a run."""

import asyncio
import json
import logging
import time
import uuid

from pydantic import ValidationError

from .artifacts import read_json
from .findings import save_findings
from .models import (
    ACTION_ADAPTER,
    AnalyzeAction,
    ConfigPatch,
    Findings,
    FinishAction,
    InspectAction,
    RunAction,
)
from .profile_query import query_profile
from .summarizer import summary_markdown


class MockBackend:
    """Deterministic smoke-test controller, never presented as a research agent."""

    async def decide(self, context, directory):
        runs = context["experiments"]
        if not context["runs_remaining"]:
            return FinishAction(rationale="Mock protocol completed the configured run budget")
        ordinal = len(runs)
        costs = [
            "ast-size",
            "bmc-cost",
            "index-aware",
            "prefer-read",
            "prefer-write",
            "prefer-constants",
            "adaptive-cost",
            "split-cost",
            "generated",
            "protocol-bmc",
        ]
        return RunAction(
            parent_run_id=runs[0]["run_id"],
            config_patch=ConfigPatch(cost_function=costs[(ordinal - 2) % len(costs)]),
            hypothesis="Mock smoke test: exercise validated configuration changes",
            expected_signal="A recorded outcome and profile",
            rationale="Protocol validation only",
        )

    async def findings(self, context, directory):
        return Findings(
            executive_summary="MOCK BACKEND: protocol smoke test, not an agent diagnosis.",
            baseline_behavior=json.dumps(context["experiments"][:2]),
            best_configuration=str(context["best_abstract_run_ids"]),
            profiling_diagnosis="Measured profiles are available in run artifacts; no causal diagnosis was performed.",
            parameter_sensitivity="The mock cycles cost functions; it does not adapt to evidence.",
            implementation_recommendation="No implementation recommendation from a mock run.",
            confidence_and_unresolved_questions="Run with the Codex backend for an actual investigation.",
            evidence_run_ids=[r["run_id"] for r in context["experiments"]],
        )


def agent_context(campaign, benchmark_id, last_result):
    context = campaign.context(benchmark_id, last_result)
    with campaign.db() as db:
        events = db.execute(
            "SELECT event_json FROM events WHERE benchmark_id=? ORDER BY event_id DESC LIMIT 16",
            (benchmark_id,),
        ).fetchall()
    with campaign.db() as db:
        actions = db.execute(
            "SELECT event_json FROM events WHERE benchmark_id=? AND json_extract(event_json, '$.kind')='agent_action' ORDER BY event_id",
            (benchmark_id,),
        ).fetchall()
    context["prior_inspections"] = [
        {key: value for key, value in json.loads(row[0])["action"].items() if key != "reason"}
        for row in actions
        if json.loads(row[0])["action"]["action"] == "INSPECT_SOURCE"
    ]
    # Retain concise evidence and previous inspection intent across stateless invocations.
    context["recent_investigation"] = [
        json.loads(row[0]) if len(row[0]) < 2500 else {"excerpt": row[0][:2500], "truncated": True}
        for row in reversed(events)
        if json.loads(row[0]).get("kind") in {"agent_action", "action_result", "rejected"}
    ]

    # Bound the two full baseline summaries; never repeat raw records.
    for key in ("baseline", "concrete"):
        if context[key] is not None:
            context[key] = summary_markdown(context[key])[:16000]
    context["documents"] = {
        p.name: p.read_text() for p in sorted((campaign.directory / "context").glob("*.md"))
    }
    return context


async def investigate(campaign, benchmark_id, backend, baseline_only=False):
    with campaign.db() as db:
        row = db.execute(
            "SELECT status FROM benchmarks WHERE benchmark_id=?", (benchmark_id,)
        ).fetchone()
        if row["status"] == "complete":
            return
        prior_actions = db.execute(
            "SELECT COUNT(*) FROM events WHERE benchmark_id=? AND json_extract(event_json, '$.kind')='decision_attempt'",
            (benchmark_id,),
        ).fetchone()[0]
    campaign.status(benchmark_id, "running")
    try:
        while len(campaign.runs(benchmark_id)) < 2:
            await campaign.run(benchmark_id)
        if baseline_only:
            campaign.status(benchmark_id, "baselines_complete")
            return
        last_result = None
        for _ in range(prior_actions, campaign.config.max_agent_actions):
            context = agent_context(campaign, benchmark_id, last_result)
            turn = (
                campaign.directory / "benchmarks" / benchmark_id / "agent-turns" / uuid.uuid4().hex
            )
            campaign.event(benchmark_id, {"kind": "decision_attempt", "turn": turn.name})
            try:
                async with campaign.agent_slots:
                    started = time.monotonic()
                    logging.getLogger(__name__).info(
                        "%s agent decision started (%d runs remaining)",
                        benchmark_id,
                        context["runs_remaining"],
                    )
                    proposed = await backend.decide(context, turn)
                    logging.getLogger(__name__).info(
                        "%s agent decision received in %.1fs",
                        benchmark_id,
                        time.monotonic() - started,
                    )
                action = ACTION_ADAPTER.validate_python(
                    proposed.model_dump() if hasattr(proposed, "model_dump") else proposed
                )
                campaign.event(
                    benchmark_id, {"kind": "agent_action", "action": action.model_dump()}
                )
                logging.getLogger(__name__).info("%s agent action: %s", benchmark_id, action.action)
                if isinstance(action, RunAction):
                    last_result = await campaign.run(benchmark_id, action)
                    # Return concise text rather than the full deterministic summary.
                    last_result = {
                        "run_id": last_result["run_id"],
                        "summary": summary_markdown(last_result["summary"])[:16000],
                    }
                elif isinstance(action, AnalyzeAction):
                    directory = campaign.run_directory(action.run_id, benchmark_id)
                    last_result = query_profile(
                        read_json(directory / "profile.json"),
                        read_json(directory / "summary.json"),
                        action.view,
                        action.filters,
                    )
                elif isinstance(action, InspectAction):
                    last_result = (
                        campaign.source.search(action.query)
                        if action.mode == "search"
                        else campaign.source.read(action.path, action.start_line, action.end_line)
                    )
                else:
                    if context["runs_remaining"] != 0:
                        raise ValueError(
                            "FINISH requires the configured execution budget; use remaining runs to test hypotheses"
                        )
                    async with campaign.agent_slots:
                        logging.getLogger(__name__).info("%s writing findings", benchmark_id)
                        findings = await backend.findings(
                            context, turn.with_name(turn.name + "-findings")
                        )
                    findings = Findings.model_validate(findings)
                    known = {r["run_id"] for r in campaign.runs(benchmark_id)}
                    if not set(findings.evidence_run_ids) <= known:
                        raise ValueError("Findings cite unknown run IDs")
                    save_findings(campaign.directory, benchmark_id, findings)
                    campaign.status(benchmark_id, "complete")
                    logging.getLogger(__name__).info("%s investigation complete", benchmark_id)
                    return
                campaign.event(benchmark_id, {"kind": "action_result", "result": last_result})
            except (ValidationError, ValueError) as exc:
                logging.getLogger(__name__).warning(
                    "%s agent action rejected: %s", benchmark_id, str(exc)[:4000]
                )
                last_result = {"rejected": str(exc)[:4000]}
                campaign.event(benchmark_id, {"kind": "rejected", "error": str(exc)[:4000]})
        raise RuntimeError("Agent action budget exhausted; inspect events before continuing")
    except Exception as exc:
        campaign.status(benchmark_id, "needs_attention", str(exc))
        raise


async def run_campaign(campaign, backend, baseline_only=False, benchmark_ids=None):
    identifiers = benchmark_ids or list(campaign.benchmarks)
    logging.getLogger(__name__).info(
        "Campaign: %d benchmarks, %d run slots, %d agent slots; reusing saved executions",
        len(identifiers),
        campaign.config.scheduler.max_parallel_runs,
        campaign.config.scheduler.max_parallel_agents,
    )
    results = await asyncio.gather(
        *(investigate(campaign, bid, backend, baseline_only) for bid in identifiers),
        return_exceptions=True,
    )
    failures = {
        bid: str(result)
        for bid, result in zip(identifiers, results)
        if isinstance(result, BaseException)
    }
    if failures:
        raise RuntimeError(f"Some benchmarks need attention: {failures}")
