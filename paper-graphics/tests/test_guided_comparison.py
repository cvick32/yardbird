import json
import tempfile
import unittest
from pathlib import Path

from guided_comparison import api_metrics, collect, read_events, render


class GuidedComparisonTests(unittest.TestCase):
    def test_costs_are_per_call_and_unanswered_requests_are_unknown(self):
        metrics = api_metrics([
            {"event": "request", "query_id": 1},
            {"event": "response", "query_id": 1, "cost": {"estimated_usd": 0.25},
             "elapsed_secs": 2, "run_cost": {"estimated_total_usd": 99}},
            {"event": "episode_end", "outcome": "violated"},
            {"event": "request", "query_id": 2},
        ])
        self.assertEqual(metrics["api_calls"], 2)
        self.assertEqual(metrics["estimated_subtotal_usd"], 0.25)
        self.assertEqual(metrics["unknown_cost_calls"], 1)
        self.assertIsNone(metrics["estimated_total_usd"])
        self.assertEqual(metrics["accepted_episodes"], 1)


    def test_conditional_jev_synthetic_result_is_not_an_extra_call(self):
        metrics = api_metrics([
            {"event": "binding_result", "query_id": 1, "cost": {"estimated_usd": 0.1}},
            {"event": "attempt_result", "query_id": 1, "cost": None},
        ])
        self.assertEqual(metrics["api_calls"], 1)
        self.assertEqual(metrics["estimated_total_usd"], 0.1)

    def test_embedded_accounting_is_authoritative_without_jsonl(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "results.json"
            runs = [f"{method}_d4" for method in ("jev", "jev-fallback", "openai", "yardbird", "z3")]
            usage = api_metrics([])
            usage.update(api_calls=2, estimated_subtotal_usd=0.2,
                         estimated_total_usd=None, unknown_cost_calls=1,
                         resolved_models=["jev-resolved"], episodes=2,
                         fallback_episodes=1, log_available=True, status="incomplete")
            path.write_text(json.dumps({
                "metadata": {"planned_runs": runs, "examples": ["a.vmt"]},
                "benchmarks": [{"example": "a.vmt", "result": [{
                    "run_name": runs[1], "result": {"Success": {}},
                    "api_usage": usage,
                }]}],
            }))
            # An invalid audit log must not affect embedded result processing.
            logs = path.with_suffix(".api")
            logs.mkdir()
            (logs / "0001-0000.jsonl").write_text("invalid JSON\n")
            rows, summaries = collect([path])
            row = next(r for r in rows if r["method"] == "jev-fallback")
            self.assertEqual(row["status"], "Success")
            self.assertEqual(row["api_usage_source"], "embedded")
            self.assertEqual(row["api_calls"], 2)
            self.assertIsNone(row["estimated_total_usd"])
            self.assertEqual(row["resolved_models"], "jev-resolved")
            self.assertEqual(row["fallback_episodes"], 1)
            self.assertEqual(len(summaries), 5)
            render([path], root / "figures")
            self.assertEqual(len(list((root / "figures").glob("*.pdf"))), 6)

    def test_partial_jsonl_only_tolerates_unfinished_final_line(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "api.jsonl"
            path.write_text('{"event":"request"}\n{"event":')
            self.assertEqual(len(read_events(path)), 1)
            path.write_text('{"event":\n')
            with self.assertRaises(json.JSONDecodeError):
                read_events(path)

    def test_partial_suite_keeps_pending_separate_and_renders_all_figures(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "results.json"
            runs = [f"{method}_d4" for method in ("jev", "openai", "yardbird", "z3")]
            path.write_text(json.dumps({
                "metadata": {"planned_runs": runs, "examples": ["a.vmt", "b.vmt"]},
                "benchmarks": [{"example": "a.vmt", "result": [{
                    "run_name": runs[0], "result": {"NoProgress": {}}, "run_time": 500,
                    "run_progress": {"deepest_completed_depth": 0}, "no_guided_fallback": True,
                }]}],
            }))
            rows, summaries = collect([path])
            self.assertEqual(len(rows), 8)
            self.assertEqual(sum(r["status"] == "Pending" for r in rows), 7)
            self.assertEqual(summaries[0]["solved"], 0)
            self.assertEqual(summaries[0]["completed"], 1)
            self.assertIsNone(summaries[0]["estimated_total_usd"])
            output = root / "figures"
            render([path], output)
            self.assertEqual(len(list(output.glob("*.pdf"))), 6)
            self.assertEqual(len(list(output.glob("*.png"))), 6)
            self.assertIn("Partial results", (output / "README.txt").read_text())


if __name__ == "__main__":
    unittest.main()
