from src.tikz_generators import CactusPlotTikzGenerator
from src.benchmark_parsing import BenchmarkParser


def test_runtime_cactus_supports_all_array_cost_functions() -> None:
    tikz = CactusPlotTikzGenerator.generate(
        {
            "Z3 Array Theory": [0.1],
            "BMC Cost": [0.2],
            "AST Size": [0.3],
            "Adaptive Cost": [0.4],
            "Split Cost": [0.5],
            "Prefer Read": [0.6],
            "Prefer Write": [0.7],
            "Prefer Constants": [0.8],
        }
    )

    assert "\\addlegendentry{Adaptive Cost}" in tikz
    assert "\\addlegendentry{Split Cost}" in tikz


def test_runtime_cactus_handles_no_solved_instances() -> None:
    tikz = CactusPlotTikzGenerator.generate({"JEV": [], "OpenAI": []})
    assert "\\addlegendentry{JEV}" in tikz
    assert "\\addlegendentry{OpenAI}" in tikz
    assert "(1," not in tikz


def test_guided_methods_have_distinct_plot_styles() -> None:
    parser = BenchmarkParser.__new__(BenchmarkParser)
    results = [parser._parse_single_result("a.vmt", {
        "strategy": "abstract", "cost_function": "bmc-cost",
        "policy": policy, "instantiation_ranker": "term-cost",
        "no_guided_fallback": True, "result": {"NoProgress": {}},
    }) for policy in ("conditional-binding", "llm-one-shot")]
    assert results[0].get_plot_style() != results[1].get_plot_style()
