from dataclasses import replace
from pathlib import Path
import csv
import tempfile

from report.completed_depths import completed_depth, generate_depth_report
from report.build_report import workbook_body
from src.analysis import build_analysis
from src.benchmark_parsing import BenchmarkResult, group_benchmark_results
from main import generate_figures


def result(progress):
    return BenchmarkResult("examples/quantified-transition-systems/generated-vmt/a.vmt",
                           "abstract", "bmc-cost", 1000, 20, "Timeout", False, 0, 0,
                           run_progress=progress)


def test_completed_depth_does_not_confuse_attempted_target_or_missing():
    assert completed_depth(None) is None
    assert completed_depth(result(None)) is None
    assert completed_depth(result({"current_depth": 8, "target_depth": 20})) is None
    assert completed_depth(result({"deepest_completed_depth": None})) == -1
    assert completed_depth(result({"deepest_completed_depth": 0, "current_depth": 1})) == 0
    assert completed_depth(result({"deepest_completed_depth": 7, "current_depth": 8})) == 7


def test_depth_graph_includes_qts_timeouts_and_csv_outcomes():
    results = [result({"deepest_completed_depth": 7, "current_depth": 8,
                       "target_depth": 20, "termination_reason": "timeout"})]
    results.append(replace(results[0], strategy="concrete", run_progress={
        "deepest_completed_depth": None, "current_depth": 0,
        "termination_reason": "counterexample"}))
    grouped, _ = group_benchmark_results(results)
    labels = {r.get_strategy_id(): r.strategy for r in results}
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory)
        (path / "assets").mkdir()
        sections, exports = generate_depth_report(grouped, labels, path)
        rows = list(csv.DictReader(Path(exports["completed_depth_csv"]).open()))
        assert rows[0]["completed_depth"] == "7"
        assert rows[0]["outcome"] == "7 (T)"
        assert rows[1]["completed_depth"] == "-1"
        assert rows[1]["outcome"] == "none (CEX@0)"
        assert "Completed BMC Depths" in "\n".join(sections)
        assert all(Path(asset).is_file() for asset in exports["completed_depth_assets"])


def test_concise_report_excludes_detailed_tables_and_solver_figures():
    r = replace(result(None), success=True, result_type="Success", used_instantiations=5)
    grouped, keys = group_benchmark_results([r])
    analysis = build_analysis(grouped, keys, r.get_strategy_id())
    manifest = {"run_id": "test", "env": "local", "status": "COMPLETED",
                "started_at": "today", "subruns": []}
    body = workbook_body(manifest, analysis, [], [], ["SOLVER DETAILS"], ["DEPTH GRAPH"], full=False)
    assert "DEPTH GRAPH" in body
    assert "SOLVER DETAILS" not in body
    assert "Analysis Artifacts" not in body
    assert "Largest Runtime" not in body
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory)
        generate_figures(grouped, keys, [r], path, full=False)
        assert {p.name for p in path.iterdir()} == {
            "runtime_cactus_plot.tex", "instantiation_cactus_plot.tex"}
