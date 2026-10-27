import contextlib
import copy
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import run


class ModelReadingTests(unittest.TestCase):
    def setUp(self):
        self.fixture = json.loads((run.HERE / "depth3.json").read_text())
        self.model = run.NativeModel(self.fixture)
        self.probes = run.suite()

    def test_captured_model_and_known_failure(self):
        self.assertEqual(self.fixture["provenance"]["model_version"], 11)
        self.assertEqual(self.model.evaluate("(Read_Int_Int a@0 i@0)"), 7)
        self.assertEqual(self.model.evaluate("(Read_Int_Int b@0 Z@3)"), 13)
        self.assertEqual(self.model.evaluate("(Read_Int_Int b@1 Z@3)"), 8)
        self.assertIs(self.model.evaluate(run.preservation()), False)
        self.assertIs(self.model.evaluate(run.preservation(value="1")), True)
        self.assertIs(self.model.evaluate(run.preservation(value="0")), False)
        self.assertIs(self.model.evaluate(run.preservation(read_index="i@0")), True)
        keys, values = run.answer_key(self.model, self.probes[-1])
        self.assertEqual(keys, [0, 2])  # Both literal zero and the source read work.
        self.assertEqual(values, [False, True, False])
        classification = [self.model.evaluate(p["expressions"][0]) for p in self.probes if p["category"] == "classification"]
        self.assertEqual(classification.count(False), 3)
        self.assertEqual(classification.count(True), 3)

    def test_z3_independently_checks_every_probe(self):
        if not shutil.which("z3"):
            self.skipTest("Z3 binary unavailable")
        report = run.verify_oracle(self.model, self.probes, shutil.which("z3"))
        self.assertGreater(report["expressions_checked"], 10)
        with patch.object(self.model, "evaluate", return_value=999):
            with self.assertRaisesRegex(ValueError, "Z3 disagreed"):
                run.verify_oracle(self.model, self.probes, shutil.which("z3"))

    def test_relevant_view_preserves_all_options_and_defaults(self):
        for probe in self.probes:
            fixture = dict(self.fixture, model=self.model.relevant(probe["expressions"]))
            reduced = run.NativeModel(fixture)
            for expression in probe["expressions"]:
                self.assertEqual(reduced.evaluate(expression), self.model.evaluate(expression))
            self.assertLess(len(fixture["model"]), len(self.fixture["model"]))
        default = self.model.relevant(["(Read_Int_Int b@1 Z@3)"])
        self.assertIn("else -> 8", default)

    def test_requests_are_independent_and_do_not_leak_answers(self):
        for probe in self.probes:
            order = list(reversed(range(len(probe["labels"]))))
            for presentation in ["native", "relevant", "tables"]:
                request = run.request_for(self.model, self.fixture, probe, presentation, order, "jev-latest")
                self.assertEqual(set(request), {"model", "state", "questions"})
                self.assertEqual(set(request["questions"]), {"answer"})
                self.assertEqual(request["questions"]["answer"]["type"], "choice")
                self.assertEqual(request["state"]["options"]["o0"], probe["labels"][-1])
                text = json.dumps(request)
                for forbidden in ["expected_choices", "oracle_values", "failure_summary", "successful_instantiations"]:
                    self.assertNotIn(forbidden, text)
                if presentation == "native":
                    self.assertEqual(request["state"]["model"], self.fixture["model"])
                elif presentation == "tables":
                    self.assertEqual(request["state"]["model"]["functions"]["Read_Int_Int"]["default"], 8)

    def test_anonymization_consistent_in_model_options_and_expressions(self):
        probe = next(p for p in self.probes if p["id"] == "compare-instances")
        request = run.request_for(self.model, self.fixture, probe, "native", [0, 1, 2], "jev-latest", True)
        self.assertNotIn("Read_Int_Int", json.dumps(request))
        model = run.NativeModel(request["state"])
        for i, original in enumerate(probe["expressions"]):
            self.assertEqual(model.evaluate(request["state"]["options"][f"o{i}"]), self.model.evaluate(original))

    def test_refinement_context_changes_only_task_description(self):
        for probe in self.probes:
            for presentation in ["native", "relevant", "tables"]:
                order = list(range(len(probe["labels"])))
                baseline = run.request_for(self.model, self.fixture, probe, presentation, order, "jev-latest")
                contextual = run.request_for(self.model, self.fixture, probe, presentation, order, "jev-latest", task_context="refinement")
                self.assertEqual(contextual["state"]["task"], run.REFINEMENT_CONTEXT + baseline["state"]["task"])
                contextual["state"]["task"] = baseline["state"]["task"]
                self.assertEqual(contextual, baseline)
                falsification = run.request_for(self.model, self.fixture, probe, presentation, order, "jev-latest", task_context="falsification")
                self.assertEqual(falsification["state"]["task"], run.FALSIFICATION_PROMPT)
                falsification["state"]["task"] = baseline["state"]["task"]
                self.assertEqual(falsification, baseline)

    def test_unknown_symbols_and_unsupported_model_shapes_fail_closed(self):
        with self.assertRaises(ValueError):
            self.model.evaluate("(Read_Int_Int missing 0)")
        for text in ["x -> (/ 1.0 2.0)\n", "Read_Int_Int -> {\n}", "x -> 1\nx -> 2\n"]:
            with self.assertRaises(ValueError):
                run.NativeModel(dict(self.fixture, model=text))

    def test_vmt_context_preserves_source_and_changes_no_other_inputs(self):
        source = (run.HERE.parent.parent / "examples/array/array_copy.vmt").read_bytes().decode("utf-8")
        for probe in self.probes:
            order = list(range(len(probe["labels"])))
            baseline = run.request_for(self.model, self.fixture, probe, "native", order, "jev-latest", task_context="falsification")
            contextual = run.request_for(self.model, self.fixture, probe, "native", order, "jev-latest", task_context="falsification", vmt_source=source)
            problem = contextual["state"].pop("problem")
            self.assertEqual(problem["source"], source)
            self.assertEqual(contextual, baseline)
            directed = run.request_for(self.model, self.fixture, probe, "native", order, "jev-latest", task_context="property-directed", vmt_source=source)
            self.assertEqual(directed["state"]["task"], run.PROPERTY_DIRECTED_PROMPT)
            directed["state"].pop("problem")
            directed["state"]["task"] = baseline["state"]["task"]
            self.assertEqual(directed, baseline)
        with self.assertRaisesRegex(ValueError, "anonymization"):
            run.request_for(self.model, self.fixture, probe, "native", order, "jev-latest", anonymize=True, vmt_source=source)

    def test_grading_accepts_all_violations_and_handles_invalid_responses(self):
        response = {"answers": {"answer": {"type": "choice", "choice": "o0", "probabilities": {"o0": .2, "o1": .5, "o2": .3}}}}
        grade = run.grade(response, ["o0", "o2"], ["o0", "o1", "o2"])
        self.assertTrue(grade["correct"])
        self.assertEqual(grade["correct_probability"], .5)
        response["answers"]["answer"]["probabilities"]["o0"] = float("nan")
        self.assertIsNone(run.grade(response, ["o0"], ["o0", "o1", "o2"])["correct_probability"])
        for malformed in [{}, {"answers": []}, {"answers": {"answer": []}},
                          {"answers": {"answer": {"type": "choice", "choice": []}}},
                          {"answers": {"answer": {"type": "choice", "choice": "bad"}}}]:
            self.assertEqual(run.grade(malformed, ["o0"], ["o0"])["status"], "invalid")
        self.assertIsNone(run.cost({}, .042, 0)["estimated_usd"])
        self.assertIsNone(run.cost({"usage": []}, .042, 0)["estimated_usd"])
        self.assertEqual(run.cost({"usage": {"input_tokens": 1000}}, .042, 0)["estimated_usd"], .000042)

    def test_ablation_inputs_preserve_model_options_and_isolate_additions(self):
        for probe in self.probes:
            order = list(range(len(probe["labels"])))
            variants = {v: run.request_for(self.model, self.fixture, probe, "native", order,
                                          "jev-latest", vmt_source="full source", ablation=v)
                        for v in run.ABLATIONS}
            for request in variants.values():
                self.assertEqual(request["state"]["model"], self.fixture["model"])
                self.assertEqual(request["state"]["problem"]["source"], "full source")
                self.assertNotIn("oracle_values", json.dumps(request))
                self.assertNotIn("expected_choices", json.dumps(request))
            base = variants["procedural"]
            directed = variants["property-directed"]
            self.assertEqual(directed["state"]["task"], run.PROPERTY_DIRECTED_PROMPT)
            directed["state"]["task"] = base["state"]["task"]
            self.assertEqual(directed, base)
            self.assertEqual(variants["procedural-examples"]["state"].pop("worked_examples"), run.WORKED_EXAMPLES)
            self.assertEqual(variants["procedural-examples"], base)
            self.assertEqual(variants["procedural-aliases"]["state"].pop("model_aliases"), self.model.aliases())
            self.assertEqual(variants["procedural-aliases"], base)

    def test_aliases_cover_every_constant_without_conflating_bool_and_int(self):
        self.model.constants.update(test_bool=True, test_int=1, test_alias=1)
        with patch.object(self.model, "evaluate", side_effect=AssertionError("No question evaluation allowed")):
            groups = self.model.aliases()["groups"]
        flattened = {name: g["value"] for g in groups for name in g["symbols"]}
        self.assertEqual(flattened, self.model.constants)
        integer_group = next(g for g in groups if "test_int" in g["symbols"])
        self.assertIn("test_alias", integer_group["symbols"])
        self.assertNotIn("test_bool", integer_group["symbols"])
        self.assertEqual(sum(len(g["symbols"]) for g in groups), len(self.model.constants))

    @unittest.skipUnless(shutil.which("z3"), "Z3 binary unavailable")
    def test_ablation_cli_pairs_options_and_answer_keys_across_variants(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(run, "JevClient") as client:
            path = Path(directory) / "ablation.jsonl"
            with contextlib.redirect_stdout(io.StringIO()):
                result = run.main(["run", "--output", str(path), "--ablation", *run.ABLATIONS,
                                   "--vmt", str(run.HERE.parent.parent / "examples/array/array_copy.vmt"),
                                   "--repeats", "3", "--shuffle-options", "--max-queries", "168"])
            self.assertEqual(result, 0)
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            self.assertEqual(rows[0]["planned_queries"], 168)
            groups = {}
            for row in rows[1:]:
                groups.setdefault((row["question"], row["trial"]), []).append(row)
            self.assertEqual(len(groups), 42)
            for group in groups.values():
                self.assertEqual({r["ablation"] for r in group}, set(run.ABLATIONS))
                for r in group:
                    self.assertEqual(r["request"]["state"]["options"], group[0]["request"]["state"]["options"])
                    self.assertEqual(r["expected_choices"], group[0]["expected_choices"])
            client.assert_not_called()

    def test_synthetic_example_arithmetic(self):
        model = run.NativeModel({"declarations": ["(declare-fun F (Int) Int)", "(declare-fun G (Int Int) Int)", "(declare-fun H (Int) Int)"],
                                 "model": "u -> 4\nv -> 4\np -> 2\nq -> 2\nF -> {\n4 -> 9\nelse -> 6\n}\nG -> {\n9 4 -> 12\nelse -> 3\n}\nH -> {\n2 -> 7\nelse -> 0\n}\n"})
        self.assertEqual(model.evaluate("(G (F u) v)"), 12)
        self.assertEqual(model.evaluate("(G (F u) 5)"), 3)
        self.assertIs(model.evaluate("(=> (not (= p q)) (= (H p) 0))"), True)
        self.assertIs(model.evaluate("(=> (= p q) (= (H p) 0))"), False)

    def test_summary_keeps_ablation_variants_separate(self):
        rows = []
        for i, variant in enumerate(("procedural", "procedural-examples")):
            rows.extend([
                {"event": "request", "query_id": i, "live": True, "ablation": variant,
                 "presentation": "native", "category": "binding", "chance_accuracy": 2 / 3},
                {"event": "result", "query_id": i, "status": "answered", "correct": bool(i),
                 "correct_probability": 0.5 + i * 0.1, "cost": {"estimated_usd": 0.001}},
            ])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "summary.jsonl"
            path.write_text("\n".join(map(json.dumps, rows)))
            report = run.summarize(path)
        groups = {r["variant"]: r for r in report["breakdown"]}
        self.assertEqual(groups["procedural"]["accuracy_answered"], 0)
        self.assertEqual(groups["procedural-examples"]["accuracy_answered"], 1)
        self.assertEqual(report["known_estimated_usd"], 0.002)

    @unittest.skipUnless(shutil.which("z3"), "Z3 binary unavailable")
    def test_offline_cli_is_reproducible_and_never_constructs_client(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(run, "JevClient") as client:
            records = []
            for name in ["a", "b"]:
                path = Path(directory) / (name + ".jsonl")
                with contextlib.redirect_stdout(io.StringIO()):
                    result = run.main(["run", "--output", str(path), "--presentation", "native", "relevant", "tables", "--shuffle-options"])
                self.assertEqual(result, 0)
                rows = [json.loads(line) for line in path.read_text().splitlines()]
                records.append(rows[1:])
                self.assertEqual(run.summarize(path)["live_requests"], 0)
                self.assertEqual(len(rows), 43)
            self.assertEqual(records[0], records[1])
            client.assert_not_called()
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                run.main(["run", "--output", str(path)])

    @unittest.skipUnless(shutil.which("z3"), "Z3 binary unavailable")
    def test_live_mock_logs_usage_and_stops_on_error(self):
        class FakeClient:
            def __init__(self):
                self.requests = []

            def decide(self, request):
                self.requests.append(copy.deepcopy(request))
                if len(self.requests) == 2:
                    raise ValueError("simulated transport failure")
                return {"answers": {"answer": {"type": "choice", "choice": "o4"}}, "usage": {"input_tokens": 1000}}

            def close(self):
                pass

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "live.jsonl"
            client = FakeClient()
            with patch.object(run, "JevClient", return_value=client), patch.object(run, "api_key", return_value="private-fixture-key"), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                result = run.main(["run", "--output", str(path), "--live", "--question", "explicit-read", "--repeats", "3"])
            self.assertEqual(result, 1)
            summary = run.summarize(path)
            self.assertEqual(summary["live_requests"], 2)
            self.assertEqual(summary["queries_with_unknown_cost"], 1)
            self.assertEqual(summary["breakdown"][0]["accuracy_all_queries"], .5)
            self.assertNotIn("private-fixture-key", path.read_text())
            self.assertNotIn("expected_choices", json.dumps(client.requests))
            # A transmitted request with no result is unknown-cost, not free.
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            path.write_text("\n".join(map(json.dumps, rows[:-1])) + '\n{"event":')
            summary = run.summarize(path)
            self.assertTrue(summary["partial_final_record"])
            self.assertEqual(summary["breakdown"][0]["outcomes"]["interrupted"], 1)


if __name__ == "__main__":
    unittest.main()
