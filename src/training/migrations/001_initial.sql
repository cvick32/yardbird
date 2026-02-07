-- Training data schema for Yardbird
-- Stores term selection decisions for training neural models on instantiation decisions.

-- Benchmarks table: metadata about each benchmark run
CREATE TABLE IF NOT EXISTS benchmarks (
    id BIGSERIAL PRIMARY KEY,
    name TEXT NOT NULL,
    cost_function TEXT NOT NULL,
    success BOOLEAN,
    total_refinements INTEGER,
    total_time_ms BIGINT,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- Decisions table: each instantiation decision point
CREATE TABLE IF NOT EXISTS decisions (
    id BIGSERIAL PRIMARY KEY,
    benchmark_id BIGINT NOT NULL REFERENCES benchmarks(id) ON DELETE CASCADE,
    bmc_depth INTEGER NOT NULL,
    axiom_name TEXT NOT NULL,
    slot_index INTEGER NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- Candidates table: terms considered for each decision
CREATE TABLE IF NOT EXISTS candidates (
    id BIGSERIAL PRIMARY KEY,
    term TEXT NOT NULL,
    decision_id BIGINT NOT NULL REFERENCES decisions(id) ON DELETE CASCADE,
    term_hash TEXT NOT NULL,
    is_constant BOOLEAN NOT NULL,
    is_variable BOOLEAN NOT NULL,
    in_property_vocab BOOLEAN NOT NULL,
    in_transition_vocab BOOLEAN NOT NULL,
    frame_index INTEGER,
    ast_size INTEGER NOT NULL,
    current_cost INTEGER NOT NULL,
    was_chosen BOOLEAN NOT NULL
);

-- Core appearances table: which term hashes appeared in unsat core
CREATE TABLE IF NOT EXISTS core_appearances (
    benchmark_id BIGINT NOT NULL REFERENCES benchmarks(id) ON DELETE CASCADE,
    term_hash TEXT NOT NULL,
    appearance_count INTEGER NOT NULL DEFAULT 1,
    PRIMARY KEY (benchmark_id, term_hash)
);

-- Indexes for common queries
CREATE INDEX IF NOT EXISTS idx_decisions_benchmark_id ON decisions(benchmark_id);
CREATE INDEX IF NOT EXISTS idx_candidates_decision_id ON candidates(decision_id);
CREATE INDEX IF NOT EXISTS idx_candidates_term_hash ON candidates(term_hash);
CREATE INDEX IF NOT EXISTS idx_core_appearances_term_hash ON core_appearances(term_hash);
CREATE INDEX IF NOT EXISTS idx_benchmarks_success ON benchmarks(success);
CREATE INDEX IF NOT EXISTS idx_benchmarks_cost_function ON benchmarks(cost_function);
