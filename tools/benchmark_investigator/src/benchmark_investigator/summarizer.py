"""Deterministic profile reductions. Timers overlap; percentages use wall time."""

from collections import Counter, defaultdict
from pathlib import Path

from .artifacts import read_json, write_json


def location(record):
    return {
        "depth": record.get("bmc_depth", record.get("depth")),
        "refinement_step": record.get("refinement_step"),
    }


def _statistics(value):
    return value.get("stats", value)


def _numbers(value):
    return {
        k: v for k, v in value.items() if isinstance(v, (int, float)) and not isinstance(v, bool)
    }


def summarize_quantifiers(profile):
    provenance = profile.get("quantifier_provenance")
    if provenance is None:
        return {
            "available": False,
            "reason": "This profile predates binder provenance; identities cannot be inferred from rule names.",
        }
    sources, rules = provenance.get("sources", {}), provenance.get("rules", {})
    observations = []
    totals = {}
    for record in profile.get("cost_records", []):
        for rule, phases in record.get("quantifier_work", {}).items():
            for phase, work in phases.items():
                observation = {
                    "rule": rule,
                    "source_id": rules.get(rule, {}).get("source_id"),
                    "phase": phase,
                    **location(record),
                    "timing_secs": work.get("timing_secs", {}),
                    "counters": work.get("counters", {}),
                }
                observations.append(observation)
                total = totals.setdefault(rule, {"timing_secs": Counter(), "counters": Counter()})
                total["timing_secs"].update(observation["timing_secs"])
                total["counters"].update(observation["counters"])
    return {
        "available": True,
        "sources": sources,
        "rules": {
            rule: {**rules.get(rule, {}), **{k: dict(v) for k, v in totals.get(rule, {}).items()}}
            for rule in sorted(set(rules) | set(totals))
        },
        "observations": observations,
    }


def summarize(
    profile: dict | None, result: dict | None = None, metadata: dict | None = None
) -> dict:
    metadata, result = metadata or {}, result or {}
    progress = result.get("run_progress") or {}
    profile_available = profile is not None
    profile = profile or {}
    wall = metadata.get("wall_time_secs", progress.get("elapsed_wall_secs"))
    outcome = {
        "termination_reason": metadata.get("termination_reason")
        or progress.get("termination_reason", "unknown"),
        "wall_time_secs": wall,
        "found_proof": result.get("found_proof", False),
        "counterexample": result.get("counterexample", False),
        "profile_available": profile_available,
        "error": metadata.get("error") or progress.get("error"),
    }
    drivers = profile.get("driver_records", [])
    costs = profile.get("cost_records", [])
    checks = profile.get("solver_checks", [])
    # Compatibility for older saved profiles; never infer proof or completion of the target.
    if not progress and drivers:
        completed = [r["bmc_depth"] for r in drivers if r.get("action") == "next_depth"]
        progress = {
            "deepest_completed_depth": max(completed, default=None),
            "current_depth": drivers[-1].get("bmc_depth"),
            "current_refinement_step": drivers[-1].get("refinement_step"),
            "inferred_from_completed_records": True,
        }
    timing = {}
    depths = defaultdict(
        lambda: {
            "refinement_steps": 0,
            "driver_secs": 0.0,
            "solver_secs": 0.0,
            "instances_added": 0,
            "candidates_generated": 0,
            "candidates_selected": 0,
            "peak_nodes": None,
            "newly_admitted_subterms": 0,
            "rule_search_rounds": 0,
        }
    )

    def timer(key, seconds, record):
        item = timing.setdefault(
            key, {"total_secs": 0.0, "max_secs": 0.0, "max_at": None, "events": 0}
        )
        item["total_secs"] += seconds
        item["events"] += 1
        if item["max_at"] is None or seconds > item["max_secs"]:
            item.update(max_secs=seconds, max_at=location(record))

    for category, records in [("driver", drivers), ("refinement", costs), ("run", [profile])]:
        for record in records:
            for key, seconds in _numbers(record.get("timing_secs", {})).items():
                timer(f"{category}.{key}", seconds, record)
    for check in checks:
        for key, ns in _numbers(check.get("timing_ns", {})).items():
            timer(f"solver.{key}", ns / 1e9, check)
    for record in drivers:
        row = depths[record["bmc_depth"]]
        row["refinement_steps"] += 1
        row["driver_secs"] += record.get("timing_secs", {}).get("driver_step_total", 0)
        row["instances_added"] += max(
            0,
            record.get("indexed_assertions_after", 0) - record.get("indexed_assertions_before", 0),
        )
    rules = {}
    counters = Counter()
    growth = []
    peak_nodes, peak_classes = None, None
    for record in costs:
        depth = record.get("bmc_depth")
        rule_data = record.get("rule_instantiation", {})
        counters.update(_numbers(record.get("counters", {})))
        for name, values in rule_data.get("by_rule", {}).items():
            row = rules.setdefault(name, {"name": name, "depth_distribution": {}})
            for key, value in _numbers(values).items():
                row[key] = row.get(key, 0) + value
            if depth is not None:
                distribution = row["depth_distribution"].setdefault(
                    str(depth), {"generated": 0, "selected": 0}
                )
                distribution["generated"] += values.get("candidates_generated", 0)
                distribution["selected"] += values.get("candidates_selected", 0)
        graph = record.get("egraph", {})
        nodes = [v for k, v in graph.items() if k.startswith("nodes_") and isinstance(v, int)]
        classes = [v for k, v in graph.items() if k.startswith("classes_") and isinstance(v, int)]
        if nodes:
            peak_nodes = max(nodes + ([peak_nodes] if peak_nodes is not None else []))
        if classes:
            peak_classes = max(classes + ([peak_classes] if peak_classes is not None else []))
        if depth is not None:
            row = depths[depth]
            row["newly_admitted_subterms"] += record.get("counters", {}).get(
                "egraph_build_newly_admitted_subterms", 0
            )
            row["rule_search_rounds"] += graph.get("rule_search_rounds") or 0
            row["candidates_generated"] += rule_data.get("candidates_generated", 0)
            row["candidates_selected"] += rule_data.get("candidates_selected", 0)
            if nodes:
                row["peak_nodes"] = max(
                    nodes + ([row["peak_nodes"]] if row["peak_nodes"] is not None else [])
                )
        before, after = graph.get("nodes_before_update"), graph.get("nodes_after_update")
        if before is not None and after is not None:
            growth.append(location(record) | {"nodes_added": after - before})
        cost_rec = record.get("cost_rec", {})
        if "total_secs" in cost_rec:
            timer("cost_function.total", cost_rec["total_secs"], record)
        for site, values in cost_rec.get("by_site", {}).items():
            timer(f"cost_function.site.{site}", values.get("secs", 0), record)
    run_statistics = _statistics(result.get("solver_statistics", {}))
    solver_counts = Counter(str(r.get("result", "unknown")).lower() for r in checks)
    statistics = Counter()
    for check in checks:
        statistics.update(_numbers(_statistics(check.get("statistics_delta", {}))))
        depths[check["depth"]]["solver_secs"] += (
            check.get("timing_ns", {}).get("raw_check", 0) / 1e9
        )
    for item in timing.values():
        item["percent_of_wall"] = 100 * item["total_secs"] / wall if wall else None

    def top(records, key, count=5):
        return sorted(records, key=key, reverse=True)[:count]

    for row in rules.values():
        row["total_secs"] = row.get("search_secs", 0) + row.get("apply_secs", 0)
    sorted_rules = sorted(rules.values(), key=lambda r: (-r["total_secs"], r["name"]))
    events = {
        "slowest_driver_steps": top(
            [
                location(r) | {"seconds": r.get("timing_secs", {}).get("driver_step_total", 0)}
                for r in drivers
            ],
            lambda r: r["seconds"],
        ),
        "slowest_solver_checks": top(
            [
                location(r)
                | {
                    "check_id": r.get("check_id"),
                    "seconds": r.get("timing_ns", {}).get("raw_check", 0) / 1e9,
                }
                for r in checks
            ],
            lambda r: r["seconds"],
        ),
        "largest_egraph_expansions": top(growth, lambda r: r["nodes_added"]),
        "largest_candidate_batches": top(
            [
                location(r)
                | {"generated": r.get("rule_instantiation", {}).get("candidates_generated", 0)}
                for r in costs
            ],
            lambda r: r["generated"],
        ),
        "most_instances_added": top(
            [
                location(r)
                | {
                    "instances": max(
                        0,
                        r.get("indexed_assertions_after", 0)
                        - r.get("indexed_assertions_before", 0),
                    )
                }
                for r in drivers
            ],
            lambda r: r["instances"],
        ),
    }
    return {
        "schema_version": 1,
        "outcome": outcome,
        "progress": progress,
        "timing": timing,
        "depths": [{"depth": d} | row for d, row in sorted(depths.items())],
        "refinement": {
            "steps": result.get("total_refinement_steps", len(drivers)),
            "instances_added": result.get("total_instantiations_added"),
            "counters": dict(counters),
        },
        "solver": {
            "checks": len(checks),
            "results": dict(solver_counts),
            "raw_check_secs": sum(c.get("timing_ns", {}).get("raw_check", 0) for c in checks) / 1e9,
            "statistics_delta_totals": dict(statistics),
            "run_statistics": run_statistics,
            "total_solver_secs": run_statistics.get(
                "total_solver_time",
                run_statistics.get(
                    "solver_time",
                    sum(c.get("timing_ns", {}).get("raw_check", 0) for c in checks) / 1e9,
                ),
            ),
        },
        "egraph": {"peak_nodes": peak_nodes, "peak_classes": peak_classes},
        "rules": sorted_rules,
        "rule_rankings": {
            "substitutions_explored": [
                r["name"]
                for r in top(sorted_rules, lambda r: r.get("substitutions_explored", 0), len(rules))
            ],
            "candidates_generated": [
                r["name"]
                for r in top(sorted_rules, lambda r: r.get("candidates_generated", 0), len(rules))
            ],
        },
        "quantifiers": summarize_quantifiers(profile),
        "events": events,
    }


def summary_markdown(summary: dict, run_id: str = "", config: dict | None = None) -> str:
    lines = [
        f"# RUN {run_id}",
        "",
        f"Config: {config or {}}",
        "",
        f"Outcome: {summary['outcome']}",
        f"Progress: {summary['progress']}",
        "",
        "Timing (overlapping scopes; percentages are of wall time):",
    ]
    for name, item in sorted(summary["timing"].items(), key=lambda kv: -kv[1]["total_secs"])[:16]:
        lines.append(
            f"- {name}: {item['total_secs']:.4f}s; max {item['max_secs']:.4f}s at {item['max_at']}"
        )
    lines += [
        "",
        f"Solver: {summary['solver']['checks']} checks; {summary['solver']['raw_check_secs']:.4f}s raw checks",
        f"E-graph: {summary['egraph']}",
        "",
        "Depths:",
    ]
    for row in summary["depths"]:
        lines.append(
            f"- {row['depth']}: {row['refinement_steps']} steps, {row['driver_secs']:.3f}s driver, {row['solver_secs']:.3f}s solver, {row['instances_added']} instances, {row['peak_nodes']} peak nodes"
        )
    lines += ["", "Dominant rules:"]
    for rule in summary["rules"][:8]:
        lines.append(
            f"- {rule['name']}: {rule['total_secs']:.4f}s; generated {rule.get('candidates_generated', 0)}, selected {rule.get('candidates_selected', 0)}"
        )
    lines += [
        "",
        f"Quantifiers: {summary['quantifiers']}",
        f"Counters: {summary['refinement']['counters']}",
        "",
        f"Events: {summary['events']}",
    ]
    return "\n".join(lines) + "\n"


def summarize_run(directory: Path) -> dict:
    summary = summarize(
        read_json(directory / "profile.json"),
        read_json(directory / "result.json"),
        read_json(directory / "metadata.json"),
    )
    write_json(directory / "summary.json", summary)
    (directory / "summary.md").write_text(
        summary_markdown(summary, directory.name, read_json(directory / "config.json"))
    )
    return summary


def ranking_key(summary: dict) -> tuple:
    reason = summary["outcome"]["termination_reason"]
    wall = summary["outcome"].get("wall_time_secs")
    solver = summary["solver"].get("total_solver_secs", summary["solver"]["raw_check_secs"])
    if reason in {"depth_limit", "proof"}:
        return (0, wall if wall is not None else float("inf"), solver)
    if reason in {"timeout", "external_timeout"}:
        p = summary["progress"]
        return (
            1,
            -_progress(p.get("deepest_completed_depth")),
            -_progress(p.get("current_depth")),
            -_progress(p.get("current_refinement_step")),
            solver,
        )
    # Counterexamples and inconclusive failures are diagnostic outcomes, not fast wins.
    return (2, reason, wall if wall is not None else float("inf"))


def _progress(value):
    return value if value is not None else -1
