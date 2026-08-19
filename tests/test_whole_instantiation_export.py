from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


EXPORTER_PATH = (
    Path(__file__).resolve().parents[1]
    / "tools"
    / "ml_ranker"
    / "export_whole_instantiations.py"
)
SPEC = importlib.util.spec_from_file_location(
    "export_whole_instantiations", EXPORTER_PATH
)
assert SPEC is not None and SPEC.loader is not None
EXPORTER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EXPORTER)


class WholeInstantiationExportTests(unittest.TestCase):
    def test_query_exports_selection_and_solver_resource_targets(self) -> None:
        query = EXPORTER.build_query("run's-version", include_unsuccessful=False)

        self.assertIn("ai.was_selected", query)
        self.assertIn("ai.in_unsat_core", query)
        self.assertIn("ai.substitution AS complete_substitution", query)
        self.assertIn("ai.indexed_assertions_deduplicated", query)
        self.assertIn('AS "resource_snapshot_rlimit_count"', query)
        self.assertIn('AS "resource_delta_solver_time"', query)
        self.assertIn("'shared_final_unsat_event_at_depth'", query)
        self.assertIn("tr.run_version = 'run''s-version'", query)
        self.assertIn("b.success IS TRUE", query)

    def test_unsuccessful_export_without_run_filter_has_no_where_clause(self) -> None:
        query = EXPORTER.build_query(None, include_unsuccessful=True)

        self.assertNotIn("WHERE b.success IS TRUE", query)
        self.assertNotIn("WHERE tr.run_version", query)

    def test_normalizes_sqlalchemy_postgres_urls(self) -> None:
        self.assertEqual(
            EXPORTER.normalize_database_url("postgresql+psycopg://host/db"),
            "postgresql://host/db",
        )


if __name__ == "__main__":
    unittest.main()
