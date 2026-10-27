import contextlib
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import intermediates
import run


class IntermediateTests(unittest.TestCase):
    def setUp(self):
        self.fixture = json.loads((run.HERE / "depth3.json").read_text())
        self.model = run.NativeModel(self.fixture)

    def test_chain_values_and_complete_array_options(self):
        chains = intermediates.chains(self.model)
        expected = {"source-read": [7, "Array_Int_Int!val!1", 8, 13, True, False, False],
                    "constant-one": [1, "Array_Int_Int!val!6", 13, 13, True, True, True]}
        for name, probes in chains.items():
            self.assertEqual([self.model.evaluate(p["expressions"][0]) for p in probes], expected[name])
            self.assertEqual(len(probes[1]["labels"]), 51)
            for probe in probes:
                self.assertEqual(len(run.answer_key(self.model, probe)[0]), 1)
        if shutil.which("z3"):
            run.verify_oracle(self.model, [p for ps in chains.values() for p in ps], shutil.which("z3"))

    def test_nested_toy_model_solutions(self):
        model = run.NativeModel({"declarations": ["(declare-fun Read (S Int) Int)", "(declare-fun Write (S Int Int) S)"],
                                 "model": "src -> S!val!2\ndst -> S!val!0\np -> 4\nq -> 6\nWrite -> {\nS!val!0 4 1 -> S!val!3\nelse -> S!val!1\n}\nRead -> {\nS!val!2 4 -> 17\nS!val!0 6 -> 29\nS!val!3 6 -> 29\nS!val!1 4 -> 17\nelse -> 31\n}\n"})
        self.assertEqual(model.evaluate("(Read src p)"), 17)
        self.assertEqual(model.evaluate("(Write dst p (Read src p))"), "S!val!1")
        self.assertEqual(model.evaluate("(Read (Write dst p (Read src p)) q)"), 31)
        self.assertEqual(model.evaluate("(Read (Write dst p 1) q)"), 29)
        self.assertIs(model.evaluate("(=> (not (= p q)) (= (Read (Write dst p (Read src p)) q) (Read dst q)))"), False)
        self.assertIs(model.evaluate("(=> (not (= p q)) (= (Read (Write dst p 1) q) (Read dst q)))"), True)

    def test_lookup_ablation_values_and_row_matching_controls(self):
        probes = intermediates.lookup_probes(self.model)
        expected = ["Array_Int_Int!val!1"] * 4 + ["Array_Int_Int!val!6", "Array_Int_Int!val!15", 8, 13, False, True]
        self.assertEqual([self.model.evaluate(ps[0]["expressions"][0]) for ps in probes.values()], expected)
        for ps in probes.values():
            self.assertEqual(len(run.answer_key(self.model, ps[0])[0]), 1)
        if shutil.which("z3"):
            run.verify_oracle(self.model, [ps[0] for ps in probes.values()], shutil.which("z3"))

    def test_views_preserve_every_entry_default_and_question(self):
        named = intermediates.named_tables(self.model)
        restored = {"constants": named["constants"], "functions": {}}
        for name, table in named["functions"].items():
            restored["functions"][name] = {
                "entries": [{"arguments": [row["arguments"][p] for p in table["parameter_order"]], "value": row["result"]}
                            for row in table["entries"]], "default": table["default"]}
        self.assertEqual(restored, self.model.tables())
        for probes in intermediates.lookup_probes(self.model).values():
            probe = probes[0]
            order = list(range(len(probe["labels"])))
            base = intermediates.make_request(self.model, self.fixture, probe, order, "jev-latest", "full VMT", "generic", "independent", [])
            for view in intermediates.VIEWS:
                request = intermediates.make_request(self.model, self.fixture, probe, order, "jev-latest", "full VMT", "generic", "independent", [], view)
                if view.endswith("-short"):
                    self.assertNotIn("Array_Int_Int!val!", json.dumps(request))
                    request = intermediates.rename_domains(request, reverse=True)
                if view.startswith("named"):
                    self.assertEqual(request["state"]["model"], named)
                    request["state"]["model"] = base["state"]["model"]
                    request["state"]["model_format"] = base["state"]["model_format"]
                if view == "grouped":
                    self.assertEqual(request["state"]["model"], intermediates.grouped_tables(self.model))
                    request["state"]["model"] = base["state"]["model"]
                    request["state"]["model_format"] = base["state"]["model_format"]
                self.assertEqual(request, base)

    def test_grouped_tables_preserve_every_tuple_and_default(self):
        with patch.object(self.model, "evaluate", side_effect=AssertionError("No evaluation in serialization")):
            grouped = intermediates.grouped_tables(self.model)
        self.assertEqual(grouped["constants"], self.model.constants)
        for name, original in self.model.functions.items():
            table = grouped["functions"][name]
            self.assertEqual(table["default"], original["default"])
            restored = {}

            def walk(node, prefix):
                if len(prefix) == len(table["argument_order"]):
                    restored[tuple(prefix)] = node
                else:
                    for key, child in node.items():
                        walk(child, [*prefix, key])

            walk(table["entries"], [])
            self.assertEqual(restored, {tuple(run.smt(v) for v in args): value for args, value in original["entries"].items()})
        write = grouped["functions"]["Write_Int_Int"]
        self.assertEqual(write["entries"]["Array_Int_Int!val!0"]["0"],
                         {"1": "Array_Int_Int!val!6", "0": "Array_Int_Int!val!15"})
        self.assertNotIn("7", write["entries"]["Array_Int_Int!val!0"]["0"])
        self.assertEqual(write["default"], "Array_Int_Int!val!1")
        for probes in intermediates.grouped_probes(self.model).values():
            run.answer_key(self.model, probes[0])

    @unittest.skipUnless(shutil.which("z3"), "Z3 binary unavailable")
    def test_grouped_experiment_preserves_all_valid_binding_choices(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(run, "JevClient") as client:
            path = Path(directory) / "grouped.jsonl"
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(intermediates.main(["--output", str(path), "--repeats", "1", "--suite", "grouped",
                                                    "--modes", "independent", "--examples", "none", "--task-context", "property-directed",
                                                    "--views", "native", "grouped"]), 0)
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            self.assertEqual(rows[0]["planned_queries"], 48)
            for r in rows[1:]:
                self.assertEqual(r["expected_choices"], r["local_expected_choices"])
                if r["chain"] == "diagnostic/choose-value":
                    self.assertEqual(len(r["expected_choices"]), 2)
                self.assertNotIn("oracle", json.dumps(r["request"]))
            client.assert_not_called()

    def test_substitution_is_syntactic_and_propagates_wrong_answers(self):
        notes = [
            {"expression": "b@0", "selected_value": "Array_Int_Int!val!0"},
            {"expression": "i@0", "selected_value": "0"},
            {"expression": "Z@3", "selected_value": "1"},
            {"expression": "(Read_Int_Int a@0 i@0)", "selected_value": "7"},
        ]
        write = "(Write_Int_Int b@0 i@0 (Read_Int_Int a@0 i@0))"
        with patch.object(self.model, "evaluate", side_effect=AssertionError("No oracle in rewriting")):
            self.assertEqual(intermediates.substituted_expression(write, notes), "(Write_Int_Int Array_Int_Int!val!0 0 7)")
        notes.append({"expression": write, "selected_value": "Array_Int_Int!val!6"})
        expr = f"(Read_Int_Int {write} Z@3)"
        rewritten = intermediates.substituted_expression(expr, notes)
        self.assertEqual(rewritten, "(Read_Int_Int Array_Int_Int!val!6 1)")
        self.assertEqual(self.model.evaluate(expr), 8)
        self.assertEqual(self.model.evaluate(rewritten), 13)
        # A mistaken answer about a literal must not rewrite other literals.
        self.assertEqual(intermediates.substituted_expression("(= 1 1)", [{"expression": "1", "selected_value": "0"}]), "(= 1 1)")

    @unittest.skipUnless(shutil.which("z3"), "Z3 binary unavailable")
    def test_substitution_run_does_not_send_oracle_corrections(self):
        class FakeClient:
            def decide(self, request):
                return {"answers": {"answer": {"type": "choice", "choice": "o0"}}, "usage": {"input_tokens": 100}}

            def close(self):
                pass

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "substitution.jsonl"
            with patch.object(run, "JevClient", return_value=FakeClient()), patch.object(run, "api_key", return_value="test-secret"), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(intermediates.main(["--live", "--output", str(path), "--repeats", "1", "--suite", "substitution",
                                                    "--modes", "independent", "substituted", "--examples", "none", "--task-context", "property-directed"]), 0)
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            histories = {}
            for r in rows:
                if r["event"] != "request":
                    continue
                key = (r["mode"], r["chain"], r["trial"])
                notes = histories.setdefault(key, [])
                actual = intermediates.substituted_expression(r["expression"], notes) if r["mode"] == "substituted" else r["expression"]
                self.assertEqual(r["evaluated_expression"], actual)
                self.assertIn(actual, r["request"]["questions"]["answer"]["instructions"])
                state = r["request"]["state"]
                self.assertEqual(state["model"], self.fixture["model"])
                self.assertEqual(state["task"], run.PROPERTY_DIRECTED_PROMPT)
                self.assertNotIn("worked_examples", state)
                self.assertNotIn("previous_answers", state)
                self.assertNotIn("oracle", json.dumps(r["request"]))
                notes.append({"expression": r["expression"], "selected_value": state["options"]["o0"]})
            report = intermediates.summarize(path)
            self.assertEqual(report["live_requests"], 40)
            self.assertEqual(len(report["chain_summary"]), 2)

    @unittest.skipUnless(shutil.which("z3"), "Z3 binary unavailable")
    def test_notes_are_only_jev_choices_and_shuffles_are_paired(self):
        class FakeClient:
            def decide(self, request):
                return {"answers": {"answer": {"type": "choice", "choice": "o0"}}, "usage": {"input_tokens": 100}}

            def close(self):
                pass

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "live.jsonl"
            with patch.object(run, "JevClient", return_value=FakeClient()), patch.object(run, "api_key", return_value="test-secret"), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(intermediates.main(["--live", "--output", str(path), "--repeats", "1",
                                                   "--views", *intermediates.VIEWS, "--max-queries", str(56 * len(intermediates.VIEWS))]), 0)
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            self.assertNotIn("test-secret", path.read_text())
            histories = {}
            shuffles = {}
            for r in rows:
                if r["event"] != "request":
                    continue
                state = r["request"]["state"]
                if r["view"].endswith("-short"):
                    state = intermediates.rename_domains(state, reverse=True)
                expected_model = (intermediates.grouped_tables(self.model) if r["view"] == "grouped" else
                                  intermediates.named_tables(self.model) if r["view"].startswith("named") else self.fixture["model"])
                self.assertEqual(state["model"], expected_model)
                self.assertNotIn("oracle_values", json.dumps(r["request"]))
                key = (r["example"], r["mode"], r["chain"], r["trial"], r["view"])
                history = histories.setdefault(key, [])
                if r["mode"] == "carried":
                    self.assertEqual(state["previous_answers"]["answers"], history)
                else:
                    self.assertNotIn("previous_answers", state)
                history.append({"expression": r["expression"], "selected_value": state["options"]["o0"]})
                paired = (r["chain"], r["trial"], r["step"])
                self.assertEqual(shuffles.setdefault(paired, state["options"]), state["options"])
            self.assertTrue(any(r.get("correct") is False for r in rows))
            self.assertEqual(intermediates.summarize(path)["live_requests"], 56 * len(intermediates.VIEWS))


if __name__ == "__main__":
    unittest.main()
