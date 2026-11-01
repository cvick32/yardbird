import json

import pytest

from guided_tables import build_data, generate, render_tex, supports, trace_metrics


def fixture(root):
    path = root / "results.json"
    methods = ["jev", "openai", "yardbird", "z3"]
    runs = [f"{m}_d50" for m in methods]
    def result(i, success):
        usage = {"api_calls": 2, "unknown_cost_calls": 1, "estimated_subtotal_usd": 1.25,
                 "estimated_total_usd": None, "episodes": 1, "accepted_episodes": 1,
                 "resolved_models": ["model_1&2"], "log_available": True,
                 "input_tokens": 100, "cached_input_tokens": 25, "output_tokens": 10}
        return {"run_name": runs[i], "depth": 50, "no_guided_fallback": True,
                "run_time": 1000 if success else 120000,
                **({"api_usage": usage} if i < 2 else {}),
                "result": {"Success": {"used_instances": ["schema", "schema"], "total_instantiations_added": 50,
                                       "total_refinement_steps": 2}} if success else {"Timeout": 120000}}
    path.write_text(json.dumps({"metadata": {"planned_runs": runs, "examples": ["a.vmt", "b.vmt"], "git_commit": "abc"},
                               "benchmarks": [{"example": "a.vmt", "result": [result(i, True) for i in range(4)]},
                                              {"example": "b.vmt", "result": [result(i, False) for i in range(4)]}]}))
    logs = path.with_suffix(".api")
    logs.mkdir()
    jev = [{"event": "candidate_result", "feedback": {"outcome": "violated"}},
           {"event": "candidate_result", "feedback": {"outcome": "instance_true"}},
           {"event": "attempt_result", "accepted_instances": 1, "cost": {"estimated_usd": 999}, "feedback": {"outcome": "violated"}}]
    llm = [{"event": "attempt_result", "accepted_instances": 1, "feedback": {"outcome": "violated"}}]
    for i, events in [(0, jev), (1, llm)]:
        for j in range(2):
            (logs / f"{i:04}-{j:04}.jsonl").write_text("".join(json.dumps(e)+"\n" for e in events))
    return path


def test_totals_distinguish_installed_schemas_assertions_and_validated_proposals(tmp_path):
    path = fixture(tmp_path)
    data = build_data([path])
    jev, llm, yardbird, z3 = data["summaries"]
    assert jev["installed_schemas_known"] == 1
    assert jev["indexed_assertions_known"] == 50
    assert jev["installed_schema_coverage"] == 1
    assert jev["checked_proposals"] == 4
    assert jev["validated_proposals"] == 2
    assert llm["checked_proposals"] == 2
    assert llm["validated_proposals"] == 2
    assert jev["estimated_subtotal_usd"] == 2.5  # embedded data, not JSONL cost
    assert jev["estimated_total_usd"] is None
    assert jev["unknown_cost_calls"] == 2
    assert jev["cache_read_percent"] == 25
    assert jev["common_solved"] == 1
    assert jev["common_solved_runtime_median_seconds"] == 1
    assert yardbird["validated_proposals"] is None
    assert z3["estimated_total_usd"] == 0
    timeout = next(r for r in data["benchmarks"] if r["method"] == "jev" and r["status"] == "Timeout")
    assert timeout["installed_schemas"] is None


def test_missing_logs_are_unknown_but_zero_call_runs_need_no_log(tmp_path):
    path = fixture(tmp_path)
    (path.with_suffix(".api") / "0000-0000.jsonl").unlink()
    data = build_data([path])
    jev = data["summaries"][0]
    assert jev["missing_validation_logs"] == 1
    assert jev["validated_proposals"] == 1
    payload = json.loads(path.read_text())
    payload["benchmarks"][0]["result"][0]["api_usage"]["api_calls"] = 0
    path.write_text(json.dumps(payload))
    jev = build_data([path])["summaries"][0]
    assert jev["missing_validation_logs"] == 0
    assert jev["trace_required_runs"] == 1


def test_outputs_escape_tex_and_flag_incomplete_totals(tmp_path):
    result = generate([fixture(tmp_path)], tmp_path / "tables")
    assert len(result["tex_paths"]) == 4
    api = (tmp_path / "tables/api_usage.tex").read_text()
    assert r"model\_1\&2" in api
    assert "2.50*" in api
    assert "1*" in (tmp_path / "tables/instantiation_stats.tex").read_text()
    assert r"\input{evaluation_summary.tex}" in (tmp_path / "tables/preview.tex").read_text()
    assert json.loads((tmp_path / "tables/table_data.json").read_text())["sources"][0]["sha256"]
    assert render_tex({"name": "x", "caption": "a%b", "headers": ["x"], "rows": [["a_b"]], "notes": "$1"}).count(r"\%") == 1


def test_truncated_trace_and_malformed_complete_validation_record(tmp_path):
    path = tmp_path / "trace.jsonl"
    path.write_text('{"event":"candidate_result","feedback":{"outcome":"violated"}}\n{"event":"request"')
    stats = trace_metrics(path, "jev")
    assert stats["validated_proposals"] == 1 and stats["trace_partial"]
    path.write_text('{"event":"candidate_result",\n')
    with pytest.raises(json.JSONDecodeError):
        trace_metrics(path, "jev")


def test_reject_duplicate_trials_and_skip_unrelated_report(tmp_path):
    path = fixture(tmp_path)
    assert supports([path])
    copy = tmp_path / "copy.json"
    copy.write_bytes(path.read_bytes())
    with pytest.raises(ValueError, match="Duplicate"):
        build_data([path, copy])
    copy.write_text(json.dumps({"metadata": {"planned_runs": ["unrelated_d50"]}}))
    assert not supports([copy])


def test_workbook_uses_identical_table_cells_and_skips_unrelated_runs(tmp_path):
    from report.build_report import guided_table_sections
    generated = generate([fixture(tmp_path)], tmp_path / "tables")
    sections = "\n".join(guided_table_sections(generated))
    assert "Known estimated API spend (USD)" in sections
    assert "2.50*" in sections
    assert guided_table_sections(None) == []
