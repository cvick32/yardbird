import json
from pathlib import Path
import tempfile
import unittest

from summarize import summarize


class CostSummaryTests(unittest.TestCase):
    def test_conditional_queries_have_distinct_costs_and_local_attempt_is_not_billed(self):
        records = []
        for query_id in (1, 2):
            records.extend([
                {"event":"request", "query_id":query_id, "attempt":1, "stage":"conditional_binding", "request_bytes":100, "policy":"conditional-binding"},
                {"event":"binding_result", "query_id":query_id, "attempt":1, "stage":"conditional_binding", "elapsed_secs":0.1,
                 "outcome":"selected", "cost":{"status":"estimated", "estimated_usd":0.001}},
            ])
        result = self.summary(records + [
            {"event":"attempt_result", "query_id":2, "attempt":1, "stage":"instantiation", "api_call":False,
             "feedback":{"outcome":"violated"}, "elapsed_secs":0.0, "cost":None},
        ])
        self.assertEqual(result["total_estimated_cost_usd"], 0.002)
        self.assertEqual(len(result["query_costs"]), 2)
        self.assertEqual(result["queries_with_unknown_cost"], 0)
        self.assertEqual(result["attempt_outcomes"], {"violated":1})
        self.assertEqual(result["policies"], ["conditional-binding"])
        self.assertAlmostEqual(result["inference_elapsed_secs"], 0.2)
        interrupted = self.summary(records + [
            {"event":"request", "query_id":3, "attempt":1, "stage":"conditional_binding", "request_bytes":100}
        ])
        self.assertEqual(interrupted["known_estimated_cost_usd"], 0.002)
        self.assertEqual(interrupted["queries_with_unknown_cost"], 1)
        skipped = self.summary(records + [
            {"event":"request", "query_id":3, "attempt":1, "stage":"conditional_binding", "request_bytes":100},
            {"event":"request_skipped", "query_id":3, "attempt":1, "stage":"conditional_binding", "outcome":"request_too_large"}
        ])
        self.assertEqual(skipped["total_estimated_cost_usd"], 0.002)

    def test_local_candidates_do_not_add_api_costs_or_attempts(self):
        result = self.summary([
            {"event": "candidate_result", "attempt": 1, "stage": "instantiation", "rank": rank,
             "matches_model_choice": rank == 1, "feedback": {"outcome": outcome}}
            for rank, outcome in [(1, "instance_true"), (2, "violated")]
        ] + [{"event": "attempt_result", "attempt": 1, "stage": "instantiation",
              "feedback": {"outcome": "violated"}, "elapsed_secs": 0.1, "validation_elapsed_secs": 0.01,
              "cost": {"status": "estimated", "estimated_usd": 0.001}}])
        self.assertEqual(result["total_estimated_cost_usd"], 0.001)
        self.assertEqual(len(result["query_costs"]), 1)
        self.assertEqual(result["candidate_outcomes"], {"instance_true": 1, "violated": 1})
        self.assertEqual(result["attempt_outcomes"], {"violated": 1})
        self.assertEqual(result["candidate_success_sources"], {"probability_search": 1})
        self.assertEqual(result["successful_candidate_ranks"], {"2": 1})

    def test_two_stages_do_not_overwrite_costs_or_count_selection_as_success(self):
        records = [
            {"event": "request", "attempt": 1, "stage": "quantifier_selection", "request_bytes": 100},
            {"event": "axiom_result", "attempt": 1, "stage": "quantifier_selection", "elapsed_secs": 0.1,
             "cost": {"status": "estimated", "estimated_usd": 0.001}},
            {"event": "request", "attempt": 1, "stage": "instantiation", "request_bytes": 200},
        ]
        result = self.summary(records)
        self.assertEqual(result["known_estimated_cost_usd"], 0.001)
        self.assertEqual(result["queries_with_unknown_cost"], 1)
        self.assertEqual(result["first_attempt_successes"], 0)
        self.assertEqual(result["attempt_outcomes"], {})
        result = self.summary(records + [{"event": "attempt_result", "attempt": 1, "stage": "instantiation",
             "feedback": {"outcome": "violated"}, "elapsed_secs": 0.2,
             "cost": {"status": "estimated", "estimated_usd": 0.002}}])
        self.assertEqual(result["total_estimated_cost_usd"], 0.003)
        self.assertEqual(len(result["query_costs"]), 2)
        self.assertEqual(result["attempt_outcomes"], {"violated": 1})
        self.assertEqual(result["first_attempt_successes"], 1)
        self.assertEqual(result["stage_outcomes"], {"quantifier_selection": {"selected": 1}, "instantiation": {"violated": 1}})
        result = self.summary(records + [
            {"event": "request_skipped", "attempt": 1, "stage": "instantiation", "outcome": "request_too_large"},
            {"event": "episode_end", "schema_version": 2, "outcome": "request_too_large", "attempts": 1}])
        self.assertEqual(result["total_estimated_cost_usd"], 0.001)
        self.assertEqual(len(result["query_costs"]), 1)

    def summary(self, records, suffix=""):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "episodes.jsonl"
            path.write_text("".join(json.dumps({"model_version": 1, **r}) + "\n" for r in records) + suffix)
            return summarize(path)

    def test_retries_are_billed_even_when_proposals_fail(self):
        result = self.summary([
            {"event": "attempt_result", "attempt": attempt,
             "feedback": {"outcome": outcome}, "elapsed_secs": 0.1,
             "cost": {"status": "estimated", "estimated_usd": 0.0000042}}
            for attempt, outcome in [(1, "instance_true"), (2, "violated")]
        ])
        self.assertEqual(result["total_estimated_cost_usd"], 0.0000084)
        self.assertEqual(len(result["query_costs"]), 2)

    def test_unknown_and_unsent_requests(self):
        request = {"event": "request", "attempt": 1, "request_bytes": 100}
        for outcome in ("dry_run", "request_too_large"):
            result = self.summary([request, {"event": "episode_end", "outcome": outcome, "attempts": 0}])
            self.assertEqual(result["total_estimated_cost_usd"], 0)
            self.assertEqual(result["query_costs"], [])
        for tail in ([], [{"event": "transport_error", "attempt": 1, "elapsed_secs": 1}],
                     [{"event": "attempt_result", "attempt": 1, "elapsed_secs": 1,
                       "feedback": {"outcome": "invalid"}}]):
            result = self.summary([request, *tail])
            self.assertIsNone(result["total_estimated_cost_usd"])
            self.assertEqual(result["queries_with_unknown_cost"], 1)
        result = self.summary([request], '{"event":')
        self.assertTrue(result["partial_final_record"])
        self.assertIsNone(result["total_estimated_cost_usd"])


if __name__ == "__main__":
    unittest.main()
