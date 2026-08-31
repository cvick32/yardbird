from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from report.build_report import (
    figure_tex_paths,
    standalone_manifest,
    table_tex_paths,
)


class ReportFragmentDiscoveryTests(unittest.TestCase):
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
