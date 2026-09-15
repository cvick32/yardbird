import copy
import json

from benchmark_investigator.models import Filters
from benchmark_investigator.profile_query import query_profile
from benchmark_investigator.summarizer import ranking_key, summarize


def test_overlapping_timers_and_statistic_deltas(profile):
    summary = summarize(profile, metadata={"wall_time_secs": 5, "termination_reason": "timeout"})
    assert summary["timing"]["driver.driver_step_total"]["total_secs"] == 5
    assert summary["timing"]["driver.strategy_sat"]["percent_of_wall"] == 60
    assert summary["timing"]["refinement.rule_matching_total"]["max_at"]["depth"] == 1
    assert summary["solver"]["raw_check_secs"] == 1
    assert summary["solver"]["statistics_delta_totals"]["conflicts"] == 6
    assert summary["refinement"]["counters"]["model_satisfied_matches_filtered"] == 8
    assert summary["rules"][0]["total_secs"] == 1
    assert summary["rules"][0]["depth_distribution"]["0"]["selected"] == 2
    assert summary["egraph"]["peak_nodes"] == 11
    assert summary["depths"][1]["instances_added"] == 2
    assert summary["progress"]["deepest_completed_depth"] == 0
    assert summary == summarize(
        copy.deepcopy(profile), metadata={"wall_time_secs": 5, "termination_reason": "timeout"}
    )


def test_missing_profile_and_quantifier_data_are_not_fabricated():
    summary = summarize(None, metadata={"termination_reason": "external_timeout"})
    assert not summary["outcome"]["profile_available"]
    assert not summary["quantifiers"]["available"]
    assert summary["progress"] == {}


def test_query_filters_depth_zero_and_bounds_large_slices(profile):
    summary = summarize(profile)
    result = query_profile(profile, summary, "refinement", Filters(depth=0))
    assert len(result["records"]["driver_records"]) == 1
    assert result["records"]["driver_records"][0]["bmc_depth"] == 0
    profile["driver_records"][0]["huge"] = "x" * 30000
    result = query_profile(profile, summary, "refinement", Filters(depth=0))
    assert result["truncated"]
    assert len(json.dumps(result)) < 25000


def test_ranking_keeps_counterexamples_and_failures_out_of_successes(profile):
    def outcome(reason, wall=10, depth=2):
        return summarize(
            profile,
            result={"run_progress": {"deepest_completed_depth": depth}},
            metadata={"termination_reason": reason, "wall_time_secs": wall},
        )

    assert ranking_key(outcome("depth_limit")) < ranking_key(outcome("timeout"))
    assert ranking_key(outcome("timeout", depth=5)) < ranking_key(outcome("timeout", depth=2))
    assert ranking_key(outcome("depth_limit", wall=1)) < ranking_key(outcome("depth_limit", wall=2))
    assert ranking_key(outcome("timeout")) < ranking_key(outcome("counterexample", wall=0.1))


def test_native_solver_statistics_include_concrete_validation_in_ranking(profile):
    result = {
        "solver_statistics": {
            "stats": {"total_solver_time": 3.0, "concrete_validation_solver_time": 2.0}
        }
    }
    summary = summarize(
        profile, result, {"termination_reason": "depth_limit", "wall_time_secs": 5.0}
    )
    assert summary["solver"]["total_solver_secs"] == 3.0
    assert summary["solver"]["statistics_delta_totals"]["conflicts"] == 6
    assert ranking_key(summary) == (0, 5.0, 3.0)


def test_native_yardbird_fixture_matches_reported_solver_totals():
    from pathlib import Path

    result = json.loads((Path(__file__).parent / "fixtures/array-copy-result.json").read_text())
    summary = summarize(result["profiling"], result)
    assert summary["solver"]["statistics_delta_totals"]["conflicts"] == 4
    assert (
        summary["solver"]["total_solver_secs"]
        == result["solver_statistics"]["stats"]["total_solver_time"]
    )
    assert summary["progress"]["deepest_completed_depth"] == 2
    assert summary["refinement"]["instances_added"] == 3
    assert summary["egraph"]["peak_nodes"] == 40


def test_quantifier_provenance_joins_work_and_filters_source_depth_phase(profile):
    profile["quantifier_provenance"] = {
        "sources": {
            "q0": {"formula": "(forall ((x Int)) ...)"},
            "q1": {"formula": "(exists ((x Int)) ...)", "parent_source_id": "q0"},
            "q2": {"formula": "(forall ((i Int)) ...)", "property_witnesses": [{"witness": "w"}]},
        },
        "rules": {"input-binder-b": {"source_id": "q1", "helper": "b"}},
    }
    for i, record in enumerate(profile["cost_records"]):
        record["quantifier_work"] = {
            "input-binder-b": {
                "conflicts": {
                    "timing_secs": {"model_filter": i + 1},
                    "counters": {"matches_examined": 10 + i, "candidates_selected": 2},
                }
            }
        }
    summary = summarize(profile)
    assert summary["quantifiers"]["available"]
    assert summary["quantifiers"]["rules"]["input-binder-b"]["counters"]["matches_examined"] == sum(
        10 + i for i in range(len(profile["cost_records"]))
    )
    sliced = query_profile(profile, summary, "quantifiers", Filters(depth=0, rule="q1"))[
        "quantifiers"
    ]
    assert set(sliced["sources"]) == {"q0", "q1"}
    assert all(r["depth"] == 0 and r["source_id"] == "q1" for r in sliced["observations"])
    assert sliced["rules"]["input-binder-b"]["counters"]["matches_examined"] == 10
    witnesses = query_profile(profile, summary, "quantifiers", Filters(rule="q2"))["quantifiers"]
    assert set(witnesses["sources"]) == {"q2"}
    assert witnesses["rules"] == {}
    assert witnesses["observations"] == []
