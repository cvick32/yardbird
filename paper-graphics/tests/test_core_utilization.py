import json
from pathlib import Path

import pytest

from core_utilization import Problem, parse, render, replay, write_reports

REPO = Path(__file__).resolve().parents[2]
SOURCE = (REPO / "examples/array/array_two_counters_replace.vmt").read_text()
SCHEMAS = [
    "(= (Read_Int_Int (Write_Int_Int a1+0 j+0 3) j+0) 3)",
    "(= (Read_Int_Int (Write_Int_Int a+0 i+0 5) i+0) 5)",
    "(=> (not (= Z j+0)) (= (Read_Int_Int (Write_Int_Int a1+0 j+0 3) Z) (Read_Int_Int a1+0 Z)))",
    "(=> (not (= Z i+0)) (= (Read_Int_Int (Write_Int_Int a+0 i+0 5) Z) (Read_Int_Int a+0 Z)))",
]


def test_reconstructs_unsat_without_historical_core():
    result = replay(SOURCE, SCHEMAS, 2)
    assert result["replay_status"] == "unsat"
    assert result["installed_schemas"] == 4
    assert result["replayed_assertions"] == 12
    assert result["core_schemas"] == 4
    assert result["schema_utilization_percent"] == 100
    assert 0 < result["core_assertions"] <= 12


@pytest.mark.parametrize("omit", range(4))
def test_incomplete_schemas_cannot_get_false_utilization(omit):
    result = replay(SOURCE, SCHEMAS[:omit] + SCHEMAS[omit + 1 :], 2)
    assert result["replay_status"] == "sat"
    assert result["schema_utilization_percent"] is None


def test_unused_schema_and_duplicates(tmp_path):
    unrelated = "(= (Read_Int_Int (ConstArr_Int_Int 99) 42) 99)"
    result = replay(
        SOURCE, SCHEMAS + [SCHEMAS[0], unrelated], 2, save_query=tmp_path / "query.smt2"
    )
    assert result["installed_schemas"] == 5
    assert result["core_schemas"] == 4
    assert result["schema_utilization_percent"] == 80
    labels = json.loads((tmp_path / "query.labels.json").read_text())
    assert all(label in labels["labels"] for label in result["core_labels"])
    # Parse the saved query independently; assumptions are explicit in its check.
    assert "(check-sat-assuming (replay_inst_" in (tmp_path / "query.smt2").read_text()


def test_relative_frame_width_and_unframed_property_index():
    problem = Problem(SOURCE)
    schema = "(= (Read_Int_Int (Write_Int_Int a+0 i+2 5) Z) 5)"
    placements = list(problem.placements(schema, 3))
    assert [end for end, _ in placements] == [2, 3]
    first = placements[0][1].sexpr()
    assert "a@0" in first and "i@2" in first and "Z@2" in first
    assert "a@1" in placements[1][1].sexpr()


def test_zero_instantiations_have_undefined_ratio():
    source = SOURCE.replace("(and a!2)", "true")
    result = replay(source, [], 2)
    assert result["replay_status"] == "unsat"
    assert result["core_schemas"] == 0
    assert result["schema_utilization_percent"] is None


def test_constant_array_source_is_abstracted():
    source = (REPO / "examples/array/array_split_08.vmt").read_text()
    problem = Problem(source)
    assert "ConstArr_Int_Int" in problem.init.sexpr()
    assert "(Array Int Int)" not in problem.base


def test_unsupported_encoding_rejected():
    with pytest.raises(ValueError, match="Only"):
        Problem(SOURCE.replace("(Array Int Int)", "(Array Int Bool)"))
    with pytest.raises(ValueError, match="Quantified"):
        Problem(SOURCE.replace("(= i 0)", "(forall ((x Int)) (= i x))"))


def test_comments_and_quoted_symbols():
    assert render(parse("; comment\n(= |x y| 1)")[0]) == "(= |x y| 1)"


def test_reports_keep_missing_and_sat_out_of_denominator(tmp_path):
    row = dict(
        method="openai",
        run_name="openai_d3",
        example="case",
        **replay(SOURCE, SCHEMAS, 2),
    )
    missing = dict(
        method="openai",
        run_name="openai_d3",
        example="missing",
        replay_depth=2,
        replay_status="missing_schemas",
    )
    write_reports(tmp_path, [row, missing])
    summary = json.loads((tmp_path / "summary.json").read_text())[0]
    assert summary["runs"] == 2 and summary["unsat_replays"] == 1
    assert summary["schema_utilization_percent"] == 100


def test_cli_replays_only_original_successes(tmp_path, monkeypatch):
    import sys
    import core_utilization as module

    raw = dict(
        run_name="openai_d3",
        depth=3,
        strategy="abstract",
        instantiation_strategy="full-unroll",
    )
    payload = dict(used_instances=SCHEMAS, total_instantiations_added=12)
    records = [
        (tmp_path / "input.json", "abcdef0", "case.vmt", i, raw, status, data)
        for i, (status, data) in enumerate(
            [("Success", payload), ("NoProgress", payload), ("Timeout", None)]
        )
    ]
    monkeypatch.setattr(module, "load_rows", lambda _: iter(records))
    calls = []

    def source(*args, **kwargs):
        calls.append(args)
        return SOURCE

    monkeypatch.setattr(module.subprocess, "check_output", source)
    monkeypatch.setattr(
        sys,
        "argv",
        ["core_utilization.py", "input.json", "--output", str(tmp_path / "out")],
    )
    module.main()
    result = json.loads((tmp_path / "out/results.json").read_text())
    assert len(result["benchmarks"]) == 1
    assert result["benchmarks"][0]["historical_status"] == "Success"
    assert len(calls) == 1
    assert result["excluded_original_outcomes"] == {
        "openai_d3": {"NoProgress": 1, "Timeout": 1}
    }


def test_cli_all_unsuccessful_skips_solver_and_clears_old_report(tmp_path, monkeypatch):
    import sys
    import core_utilization as module

    raw = dict(run_name="jev_d50", depth=50)
    records = [
        (
            tmp_path / "input.json",
            None,
            "case.vmt",
            0,
            raw,
            "NoProgress",
            dict(used_instances=SCHEMAS),
        )
    ]
    monkeypatch.setattr(module, "load_rows", lambda _: iter(records))

    def unexpected(*args, **kwargs):
        pytest.fail("Unsuccessful run must not load source or invoke replay")

    monkeypatch.setattr(module.subprocess, "check_output", unexpected)
    monkeypatch.setattr(module, "replay", unexpected)
    (tmp_path / "benchmarks.csv").write_text("stale,previous,results\n")
    monkeypatch.setattr(
        sys, "argv", ["core_utilization.py", "input.json", "--output", str(tmp_path)]
    )
    module.main()
    result = json.loads((tmp_path / "results.json").read_text())
    assert result["benchmarks"] == []
    assert result["excluded_original_outcomes"] == {"jev_d50": {"NoProgress": 1}}
    assert json.loads((tmp_path / "summary.json").read_text()) == []
    assert (tmp_path / "benchmarks.csv").read_text().splitlines() == [
        "method,run_name,example,historical_status,replay_status"
    ]
