from __future__ import annotations

import contextlib
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("z3_builder", HERE / "z3_builder.py")
assert SPEC and SPEC.loader
z3_builder = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(z3_builder)


class Z3BuilderTests(unittest.TestCase):
    def test_config_pins_release_build_and_smoke_results(self) -> None:
        config = json.loads((HERE / "config.json").read_text())
        self.assertEqual(config["pinned"]["version"], "4.16.0.0")
        self.assertEqual(config["cmake"]["CMAKE_BUILD_TYPE"], "Release")
        self.assertEqual(
            [query["results"] for query in config["queries"]],
            [["sat"], ["unsat"], ["sat", "unsat", "sat"]],
        )

    def test_solver_results_ignores_other_output(self) -> None:
        self.assertEqual(
            z3_builder.solver_results('sat\n(error "example")\nunsat\n'),
            ["sat", "unsat"],
        )

    def test_compare_runs_both_binaries_on_the_same_query(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            solver = root / "z3"
            solver.write_text("#!/bin/sh\nprintf 'sat\\n'\n")
            solver.chmod(0o755)
            result = z3_builder.compare(
                {
                    "stock": {"binary": str(solver)},
                    "instrumented": {"binary": str(solver)},
                },
                {
                    "queries": [
                        {
                            "file": "queries/sat.smt2",
                            "results": ["sat"],
                        }
                    ]
                },
                runs=2,
                timeout=5,
            )
        self.assertTrue(result["results_equal"])
        self.assertEqual(result["results"], {"queries/sat.smt2": ["sat"]})

    def test_verbose_build_output_does_not_pollute_stdout_pipeline(self) -> None:
        with tempfile.TemporaryFile(mode="w+") as stdout:
            with tempfile.TemporaryFile(mode="w+") as stderr:
                with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(
                    stderr
                ):
                    z3_builder.run(
                        [
                            sys.executable,
                            "-c",
                            "import sys; print('build stdout'); "
                            "print('build stderr', file=sys.stderr)",
                        ],
                        show=True,
                    )
                stdout.seek(0)
                stderr.seek(0)
                self.assertEqual(stdout.read(), "")
                progress = stderr.read()
                self.assertIn("build stdout", progress)
                self.assertIn("build stderr", progress)


if __name__ == "__main__":
    unittest.main()
