from src.tikz_generators import CactusPlotTikzGenerator


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
