"""Check Garden's saved invocation against the file its child actually receives."""

import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class GardenOptionsTests(unittest.TestCase):
    @unittest.skipUnless(os.name == "posix", "uses a shell wrapper")
    def test_report_matches_child_options_and_guidance(self):
        build = subprocess.check_output(
            [
                "cargo",
                "build",
                "-p",
                "garden",
                "-p",
                "yardbird",
                "--bins",
                "--message-format=json",
            ],
            cwd=ROOT,
            text=True,
        )
        binaries = {
            entry["target"]["name"]: entry["executable"]
            for line in build.splitlines()
            if (entry := json.loads(line)).get("executable")
        }
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            garden = root / "garden"
            shutil.copy2(binaries["garden"], garden)
            wrapper = root / "yardbird"
            wrapper.write_text(
                '#!/bin/sh\nset -eu\ntest "$1" = --options-json\ncp "$2" "$CAPTURE"\n'
                + f'exec {shlex.quote(binaries["yardbird"])} "$@"\n'
            )
            wrapper.chmod(0o755)
            (root / "guided.vmt").write_text("""
                (declare-fun a () (Array Int Int))
                (define-fun init () Bool (! (forall ((i Int)) (= (select a i) 0)) :init true))
                (define-fun trans () Bool (! true :trans true))
                (define-fun prop () Bool (! (= (select (store a 1 7) 1) 7) :invar-property 0))
            """)
            config = root / "config.yaml"
            capture = root / "received.json"
            output = root / "result.json"
            for overrides, database_args in [
                ({}, []),
                (
                    {"guidance_work": 321, "guidance_schedule": "supplement"},
                    ["--database-url", "postgresql://example.invalid/test"],
                ),
            ]:
                with self.subTest(overrides=overrides):
                    config.write_text(
                        json.dumps(
                            {
                                "individual_configs": [
                                    dict(
                                        name="guided",
                                        strategy="abstract",
                                        cost_function="bmc-cost",
                                        policy="countermodel-guided",
                                        depth=1,
                                        **overrides,
                                    )
                                ]
                            }
                        )
                    )
                    subprocess.run(
                        [
                            garden,
                            "--config",
                            config,
                            root,
                            "--profile",
                            "--output",
                            output,
                            *database_args,
                        ],
                        cwd=ROOT,
                        check=True,
                        env={**os.environ, "CAPTURE": str(capture)},
                    )
                    row = json.loads(output.read_text())["benchmarks"][0]["result"][0]
                    received = json.loads(capture.read_text())
                    self.assertTrue(received["progress_file"])
                    if database_args:
                        self.assertEqual(received["database_url"], database_args[1])
                        received["database_url"] = "[redacted]"
                    self.assertEqual(row["options_json"], received)
                    records = row["result"]["Success"]["profiling"]["cost_records"]
                    allowance, followup = next(
                        (turn["allowance"], following["operation"])
                        for record in records
                        for turn, following in zip(
                            record["effort"], record["effort"][1:]
                        )
                        if turn["operation"] == "CountermodelCandidates"
                        and turn["report"]["selected"]
                    )
                    self.assertEqual(row["guidance_work"], allowance["dependency_work"])
                    self.assertEqual(
                        row["guidance_schedule"],
                        {
                            "DiscoverDependencies": "supplement",
                            "ReturnToDriver": "immediate",
                        }[followup],
                    )


if __name__ == "__main__":
    unittest.main()
