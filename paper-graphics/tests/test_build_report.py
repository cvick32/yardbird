from __future__ import annotations

import tempfile
import unittest
import contextlib
import io
from pathlib import Path

from main import generate_figures, strategy_artifact_key
from src.benchmark_parsing import BenchmarkResult, group_benchmark_results
from report.build_report import (
    figure_tex_paths,
    standalone_manifest,
    table_tex_paths,
)


class ReportFragmentDiscoveryTests(unittest.TestCase):
    def test_artifact_keys_preserve_short_names_and_bound_utf8_bytes(self) -> None:
        self.assertEqual(
            strategy_artifact_key("abstract_bmc-cost"), "abstract_bmc-cost"
        )
        key = "é" * 200
        bounded = strategy_artifact_key(key)
        self.assertLessEqual(len(bounded.encode("utf-8")), 128)
        self.assertEqual(strategy_artifact_key(key), bounded)
        self.assertNotEqual(strategy_artifact_key(key + "x"), bounded)

    def test_auxiliary_configurations_generate_distinct_bounded_filenames(self) -> None:
        results = []
        for trigger in [None, "detect", "manual-after-n"]:
            results.append(
                BenchmarkResult(
                    example_name="examples/array/a.vmt",
                    strategy="concrete" if trigger is None else "abstract",
                    cost_function="bmc-cost",
                    runtime_ms=2000,
                    depth=50,
                    result_type="Success",
                    success=True,
                    used_instantiations=10,
                    num_checks=2,
                    solver="z3",
                    egraph_builder="source-then-full",
                    instantiation_ranker="prefer-source",
                    candidate_winners_per_group=16,
                    property_check_mode="assumptions",
                    instantiation_strategy="full-unroll",
                    preprocess_exact_read_after_write=False,
                    abstract_recurrent_products=False,
                    synthesis_trigger=trigger,
                    synthesis_guard_policy="interpolant",
                    synthesis_after=10 if trigger == "manual-after-n" else None,
                    solver_time_s=1.0,
                    solver_stats={"added eqs": 10},
                )
            )
        grouped, keys = group_benchmark_results(results)
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            with contextlib.redirect_stdout(io.StringIO()):
                generate_figures(grouped, keys, results, output)
            stat_files = list(output.glob("solver_stat_added_equalities_*.tex"))
            self.assertEqual(len(stat_files), 2)
            self.assertTrue(
                all(len(p.name.encode("utf-8")) <= 200 for p in output.iterdir())
            )
            contents = "\n".join(p.read_text() for p in stat_files)
            for key in keys:
                if key.startswith("abstract"):
                    self.assertIn(key, contents)

    def test_comment_only_figure_is_not_compiled_or_treated_as_a_table(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            tex_dir = Path(temporary)
            placeholder = tex_dir / "instantiation_cactus_plot.tex"
            placeholder.write_text("% No successful runs to plot\n")
            figure = tex_dir / "runtime_cactus_plot.tex"
            figure.write_text("\\begin{tikzpicture}\n\\end{tikzpicture}\n")
            table = tex_dir / "summary_statistics.tex"
            table.write_text("\\begin{tabular}{c}value\\end{tabular}\n")

            self.assertEqual(figure_tex_paths(tex_dir), [figure])
            self.assertEqual(table_tex_paths(tex_dir), [table])

    def test_standalone_result_manifest_is_reportable(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            result = root / "result.json"
            result.write_text("{}")
            manifest = standalone_manifest([result], root / "ablation", "Ablation")

        self.assertEqual(manifest["name"], "Ablation")
        self.assertEqual(manifest["status"], "COMPLETED")
        self.assertEqual(manifest["subruns"][0]["result_path"], str(result.resolve()))


if __name__ == "__main__":
    unittest.main()
