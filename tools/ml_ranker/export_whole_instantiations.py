#!/usr/bin/env python3
"""Export complete array-instantiation candidates with solver-resource targets."""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path


RESOURCE_KEYS = (
    "rlimit count",
    "decisions",
    "added eqs",
    "mk clause",
    "mk bool var",
    "conflicts",
    "propagations",
    "solver_time",
)


def sql_literal(value: str) -> str:
    return "'" + value.replace("'", "''") + "'"


def load_dotenv(repo_root: Path) -> None:
    env_path = repo_root / ".env"
    if not env_path.exists():
        return
    for raw_line in env_path.read_text().splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        os.environ.setdefault(key.strip(), value.strip().strip("'\""))


def build_query(training_run: str | None, include_unsuccessful: bool) -> str:
    filters: list[str] = []
    if training_run:
        filters.append(f"tr.run_version = {sql_literal(training_run)}")
    if not include_unsuccessful:
        filters.append("b.success IS TRUE")
    where_clause = f"WHERE {' AND '.join(filters)}" if filters else ""

    snapshot_columns = ",\n        ".join(
        f"COALESCE((ue.solver_stats_snapshot ->> {sql_literal(key)})::DOUBLE PRECISION, 0) "
        f'AS "resource_snapshot_{key.replace(" ", "_")}"'
        for key in RESOURCE_KEYS
    )
    delta_columns = ",\n        ".join(
        f"COALESCE((ue.solver_stats_delta ->> {sql_literal(key)})::DOUBLE PRECISION, 0) "
        f'AS "resource_delta_{key.replace(" ", "_")}"'
        for key in RESOURCE_KEYS
    )

    return f"""
COPY (
WITH chosen_bindings AS (
    SELECT
        aid.abstract_instantiation_id,
        COUNT(*) AS binding_count,
        SUM(c.ast_size) AS chosen_binding_ast_size_sum,
        MAX(c.ast_size) AS chosen_binding_ast_size_max,
        SUM(c.current_cost) AS chosen_binding_cost_sum,
        MAX(c.current_cost) AS chosen_binding_cost_max,
        COUNT(*) FILTER (WHERE c.is_constant) AS chosen_constant_bindings,
        COUNT(*) FILTER (WHERE c.is_variable) AS chosen_variable_bindings,
        COUNT(*) FILTER (WHERE c.in_property_vocab) AS chosen_property_bindings,
        COUNT(*) FILTER (WHERE c.in_transition_vocab) AS chosen_transition_bindings,
        MIN(c.frame_index) AS chosen_min_frame,
        MAX(c.frame_index) AS chosen_max_frame,
        STRING_AGG(d.variable || '=' || c.term, ' || ' ORDER BY d.variable, d.id) AS chosen_binding_terms
    FROM abstract_instantiation_decisions aid
    JOIN decisions d ON d.id = aid.decision_id
    JOIN candidates c ON c.decision_id = d.id AND c.was_chosen
    GROUP BY aid.abstract_instantiation_id
),
candidate_rows AS (
    SELECT
        tr.run_version AS training_run,
        tr.git_commit,
        tr.dirty_worktree,
        b.id AS benchmark_id,
        b.name AS benchmark_name,
        b.success AS benchmark_success,
        ai.id AS abstract_instantiation_db_id,
        ai.abstract_instantiation_id,
        ai.term AS complete_term,
        ai.term_hash AS complete_term_hash,
        ai.axiom_name,
        ai.bmc_depth,
        ai.refinement_step,
        ai.substitution AS complete_substitution,
        ai.was_selected,
        ai.in_unsat_core,
        ai.indexed_assertions_attempted,
        ai.indexed_assertions_added,
        ai.indexed_assertions_deduplicated,
        ai.helper_assertions_attempted,
        ai.helper_assertions_added,
        ai.helper_assertions_deduplicated,
        COUNT(*) OVER (
            PARTITION BY ai.benchmark_id, ai.bmc_depth, ai.refinement_step
        ) AS complete_candidate_pool_size,
        COALESCE(cb.binding_count, 0) AS binding_count,
        COALESCE(cb.chosen_binding_ast_size_sum, 0) AS chosen_binding_ast_size_sum,
        COALESCE(cb.chosen_binding_ast_size_max, 0) AS chosen_binding_ast_size_max,
        COALESCE(cb.chosen_binding_cost_sum, 0) AS chosen_binding_cost_sum,
        COALESCE(cb.chosen_binding_cost_max, 0) AS chosen_binding_cost_max,
        COALESCE(cb.chosen_constant_bindings, 0) AS chosen_constant_bindings,
        COALESCE(cb.chosen_variable_bindings, 0) AS chosen_variable_bindings,
        COALESCE(cb.chosen_property_bindings, 0) AS chosen_property_bindings,
        COALESCE(cb.chosen_transition_bindings, 0) AS chosen_transition_bindings,
        cb.chosen_min_frame,
        cb.chosen_max_frame,
        cb.chosen_binding_terms,
        ue.event_index AS target_unsat_event_index,
        ue.core_size AS target_core_size,
        {snapshot_columns},
        {delta_columns}
    FROM abstract_instantiations ai
    JOIN benchmarks b ON b.id = ai.benchmark_id
    LEFT JOIN training_runs tr ON tr.id = b.training_run_id
    LEFT JOIN chosen_bindings cb ON cb.abstract_instantiation_id = ai.id
    LEFT JOIN LATERAL (
        SELECT event_index, core_size, solver_stats_snapshot, solver_stats_delta
        FROM unsat_events
        WHERE benchmark_id = ai.benchmark_id
          AND bmc_depth = ai.bmc_depth
        ORDER BY event_index DESC
        LIMIT 1
    ) ue ON TRUE
    {where_clause}
)
SELECT
    *,
    'shared_final_unsat_event_at_depth' AS resource_target_scope
FROM candidate_rows
ORDER BY training_run, benchmark_id, bmc_depth, refinement_step,
         abstract_instantiation_db_id
) TO STDOUT WITH CSV HEADER
"""


def normalize_database_url(database_url: str) -> str:
    if database_url.startswith("postgresql+"):
        return "postgresql://" + database_url.split("://", 1)[1]
    return database_url


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Export whole-instantiation candidates and the final solver-resource "
            "snapshot/delta at their BMC depth"
        )
    )
    parser.add_argument("--database-url")
    parser.add_argument(
        "--training-run", help="Optional training_runs.run_version filter"
    )
    parser.add_argument("--include-unsuccessful", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    load_dotenv(repo_root)
    database_url = (
        args.database_url
        or os.environ.get("YARDBIRD_DATABASE_URL")
        or os.environ.get("DATABASE_URL")
    )
    if not database_url:
        parser.error("provide --database-url or set YARDBIRD_DATABASE_URL")
    database_url = normalize_database_url(database_url)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    query = build_query(args.training_run, args.include_unsuccessful)
    try:
        with args.output.open("w") as output:
            process = subprocess.run(
                [
                    "psql",
                    database_url,
                    "-X",
                    "-q",
                    "-v",
                    "ON_ERROR_STOP=1",
                    "-c",
                    query,
                ],
                check=False,
                stdout=output,
                stderr=subprocess.PIPE,
                text=True,
            )
    except FileNotFoundError as error:
        raise SystemExit("psql was not found on PATH") from error
    if process.returncode != 0:
        args.output.unlink(missing_ok=True)
        sys.stderr.write(process.stderr)
        return process.returncode

    print(f"wrote whole-instantiation dataset to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
