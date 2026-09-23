-- Versioned observations. Check/decision indices are local to a benchmark.
-- A subsequent check is temporal association, not causal proof credit.
CREATE TABLE IF NOT EXISTS policy_solver_checks (
    benchmark_id BIGINT NOT NULL REFERENCES benchmarks(id) ON DELETE CASCADE,
    check_id BIGINT NOT NULL,
    schema_version INTEGER NOT NULL,
    record JSONB NOT NULL,
    PRIMARY KEY (benchmark_id, check_id)
);

CREATE TABLE IF NOT EXISTS effort_decisions (
    benchmark_id BIGINT NOT NULL REFERENCES benchmarks(id) ON DELETE CASCADE,
    decision_index BIGINT NOT NULL,
    parent_decision_index BIGINT,
    preceding_check_id BIGINT,
    subsequent_check_id BIGINT,
    schema_version INTEGER NOT NULL,
    record JSONB NOT NULL,
    PRIMARY KEY (benchmark_id, decision_index),
    FOREIGN KEY (benchmark_id, parent_decision_index)
        REFERENCES effort_decisions(benchmark_id, decision_index),
    FOREIGN KEY (benchmark_id, preceding_check_id)
        REFERENCES policy_solver_checks(benchmark_id, check_id),
    FOREIGN KEY (benchmark_id, subsequent_check_id)
        REFERENCES policy_solver_checks(benchmark_id, check_id)
);

CREATE TABLE IF NOT EXISTS effort_candidates (
    benchmark_id BIGINT NOT NULL,
    decision_index BIGINT NOT NULL,
    abstract_instantiation_id TEXT NOT NULL,
    abstract_instantiation_db_id BIGINT REFERENCES abstract_instantiations(id) ON DELETE SET NULL,
    selected BOOLEAN NOT NULL,
    PRIMARY KEY (benchmark_id, decision_index, abstract_instantiation_id),
    FOREIGN KEY (benchmark_id, decision_index)
        REFERENCES effort_decisions(benchmark_id, decision_index) ON DELETE CASCADE
);

CREATE TABLE IF NOT EXISTS policy_installations (
    benchmark_id BIGINT NOT NULL REFERENCES benchmarks(id) ON DELETE CASCADE,
    installation_index BIGINT NOT NULL,
    preceding_check_id BIGINT,
    subsequent_check_id BIGINT,
    abstract_instantiation_id TEXT,
    record JSONB NOT NULL,
    PRIMARY KEY (benchmark_id, installation_index),
    FOREIGN KEY (benchmark_id, preceding_check_id)
        REFERENCES policy_solver_checks(benchmark_id, check_id),
    FOREIGN KEY (benchmark_id, subsequent_check_id)
        REFERENCES policy_solver_checks(benchmark_id, check_id)
);

CREATE TABLE IF NOT EXISTS policy_run_outcomes (
    benchmark_id BIGINT PRIMARY KEY REFERENCES benchmarks(id) ON DELETE CASCADE,
    schema_version INTEGER NOT NULL,
    record JSONB NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_effort_candidates_instance
    ON effort_candidates(benchmark_id, abstract_instantiation_id);
CREATE INDEX IF NOT EXISTS idx_policy_installations_instance
    ON policy_installations(benchmark_id, abstract_instantiation_id);
