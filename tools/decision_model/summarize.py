#!/usr/bin/env python3
"""Summarize complete and interrupted Jev reasoning episodes without dependencies."""
import argparse
from collections import Counter
from decimal import Decimal
import json
from pathlib import Path


def summarize(path: Path) -> dict:
    episodes = {}
    failure_counts = Counter()
    request_sizes = []
    latency = 0.0
    incomplete_line = False
    queries = {}
    stage_outcomes = {}
    stage_latency = Counter()
    stage_requests = Counter()
    candidate_outcomes = Counter()
    successful_candidate_ranks = Counter()
    candidate_success_sources = Counter()
    validation_latency = 0.0
    lines = path.read_text().splitlines()
    for index, line in enumerate(lines):
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            if index != len(lines) - 1:
                raise
            incomplete_line = True
            break
        episode = episodes.setdefault(record["model_version"], {})
        event = record["event"]
        stage = record.get("stage", "joint")
        key = (record["model_version"], record.get("attempt"), stage)
        if event == "episode_end":
            episode.update(record)
        elif event == "request":
            request_sizes.append(record["request_bytes"])
            stage_requests[stage] += 1
            queries[key] = {
                "model_version": record["model_version"],
                "attempt": record["attempt"],
                "stage": stage,
                "estimated_usd": None,
                "status": "unknown",
            }
        elif event == "attempt_result":
            validation_latency += record.get("validation_elapsed_secs", 0.0)
            outcome = record["feedback"]["outcome"]
            failure_counts[outcome] += 1
            latency += record["elapsed_secs"]
            episode["had_answer"] = True
            if outcome == "violated" and record["attempt"] == 1:
                episode["first_attempt_success"] = True
        elif event == "axiom_result":
            latency += record["elapsed_secs"]
            episode["had_answer"] = True
        elif event == "transport_error":
            latency += record["elapsed_secs"]
        elif event == "candidate_result":
            outcome = record["feedback"]["outcome"]
            candidate_outcomes[outcome] += 1
            if outcome == "violated":
                successful_candidate_ranks[str(record["rank"])] += 1
                source = "model_choice" if record["matches_model_choice"] else "probability_search"
                candidate_success_sources[source] += 1
        if event in ("attempt_result", "axiom_result", "transport_error"):
            stage_latency[stage] += record["elapsed_secs"]
            outcome = record["feedback"]["outcome"] if event == "attempt_result" else (
                "selected" if event == "axiom_result" else "transport_error")
            stage_outcomes.setdefault(stage, Counter())[outcome] += 1
            queries.setdefault(key, {"model_version": key[0], "attempt": key[1], "stage": stage}).update(
                record.get("cost", {"status": "unknown", "estimated_usd": None})
            )
        elif event == "request_skipped":
            queries.pop(key, None)
        elif event == "episode_end" and record.get("schema_version", 1) < 2 and record["outcome"] in ("dry_run", "request_too_large"):
            # The last request was logged but never transmitted.
            key = (record["model_version"], record["attempts"] + 1, "joint")
            queries.pop(key, None)
    outcomes = Counter(e.get("outcome", "interrupted") for e in episodes.values())
    costs = [q["estimated_usd"] for q in queries.values() if q.get("estimated_usd") is not None]
    known_cost = float(sum((Decimal(str(cost)) for cost in costs), Decimal(0)))
    unknown_costs = len(queries) - len(costs)
    stage_costs = {}
    for query in queries.values():
        amount = query.get("estimated_usd")
        if amount is not None:
            stage = query["stage"]
            stage_costs[stage] = stage_costs.get(stage, Decimal(0)) + Decimal(str(amount))
    return {
        "log": str(path),
        "episodes": len(episodes),
        "episode_outcomes": dict(outcomes),
        "episodes_with_model_answers": sum(bool(e.get("had_answer")) for e in episodes.values()),
        "first_attempt_successes": sum(bool(e.get("first_attempt_success")) for e in episodes.values()),
        "verified_successes_within_budget": outcomes["violated"],
        "attempt_outcomes": dict(failure_counts),
        "candidate_outcomes": dict(candidate_outcomes),
        "successful_candidate_ranks": dict(successful_candidate_ranks),
        "candidate_success_sources": dict(candidate_success_sources),
        "candidate_validation_elapsed_secs": validation_latency,
        "inference_elapsed_secs": latency,
        "request_count_including_unsent": len(request_sizes),
        "max_request_bytes": max(request_sizes, default=0),
        "partial_final_record": incomplete_line,
        "query_costs": list(queries.values()),
        "stage_outcomes": {stage: dict(counts) for stage, counts in stage_outcomes.items()},
        "requests_by_stage_including_unsent": dict(stage_requests),
        "inference_elapsed_secs_by_stage": dict(stage_latency),
        "known_estimated_cost_usd_by_stage": {stage: float(cost) for stage, cost in stage_costs.items()},
        "known_estimated_cost_usd": known_cost,
        "queries_with_unknown_cost": unknown_costs,
        "total_estimated_cost_usd": None if unknown_costs else known_cost,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("logs", type=Path, nargs="+")
    args = parser.parse_args()
    print(json.dumps([summarize(path) for path in args.logs], indent=2))
