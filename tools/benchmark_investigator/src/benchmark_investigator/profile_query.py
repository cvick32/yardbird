"""Bounded, explicit profile slices; never inject the entire raw profile."""

import json

from .models import Filters
from .summarizer import summarize


def query_profile(profile, summary: dict, view: str, filters: Filters) -> dict:
    if profile is None:
        return {"available": False, "outcome": summary["outcome"]}

    def selected(record):
        return (
            filters.depth is None or record.get("bmc_depth", record.get("depth")) == filters.depth
        ) and (
            filters.refinement_step is None
            or record.get("refinement_step") == filters.refinement_step
        )

    sliced = {
        key: [r for r in profile.get(key, []) if selected(r)]
        for key in ("driver_records", "cost_records", "solver_checks")
    }
    if filters.depth is None and filters.refinement_step is None:
        sliced["timing_secs"] = profile.get("timing_secs", {})
    if "quantifier_provenance" in profile:
        sliced["quantifier_provenance"] = profile["quantifier_provenance"]
    reduced = summarize(sliced, metadata=summary["outcome"])
    if view == "overview":
        payload = {k: summary[k] for k in ("outcome", "progress", "solver", "egraph")}
    elif view == "depth":
        payload = {"depths": reduced["depths"]}
    elif view == "refinement":
        payload = {"records": sliced}
    elif view == "rules":
        payload = {
            "rules": [
                r for r in reduced["rules"] if filters.rule is None or r["name"] == filters.rule
            ]
        }
    elif view == "quantifiers":
        quantifiers = reduced["quantifiers"]
        if filters.rule is not None and quantifiers["available"]:
            rule_names = {
                name
                for name, rule in quantifiers["rules"].items()
                if name == filters.rule or rule.get("source_id") == filters.rule
            }
            sources = quantifiers["sources"]
            source_ids = {
                rule["source_id"]
                for name, rule in quantifiers["rules"].items()
                if name in rule_names and rule.get("source_id")
            }
            if filters.rule in sources:
                source_ids.add(filters.rule)
            # Retain parent formulas so nested binders remain intelligible.
            pending = list(source_ids)
            while pending:
                parent = sources.get(pending.pop(), {}).get("parent_source_id")
                if parent is not None and parent not in source_ids:
                    source_ids.add(parent)
                    pending.append(parent)
            quantifiers = {
                **quantifiers,
                "sources": {name: value for name, value in sources.items() if name in source_ids},
                "rules": {
                    name: value
                    for name, value in quantifiers["rules"].items()
                    if name in rule_names
                },
                "observations": [
                    row for row in quantifiers["observations"] if row["rule"] in rule_names
                ],
            }
        payload = {"quantifiers": quantifiers}
    elif view == "solver":
        payload = {"aggregate": reduced["solver"], "checks": sliced["solver_checks"]}
    else:
        payload = {view: reduced[view]}
    # Return valid JSON with an explicit truncation marker, never a broken JSON prefix.
    encoded = json.dumps(payload, sort_keys=True)
    if len(encoded) > 24000:
        return {
            "truncated": True,
            "hint": "Narrow depth/refinement/rule filters",
            "excerpt": encoded[:10000],
        }
    return {"truncated": False, **payload}
