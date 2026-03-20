-- Instantiation provenance schema additions.

ALTER TABLE decisions
ADD COLUMN IF NOT EXISTS decision_key TEXT;

CREATE TABLE IF NOT EXISTS abstract_instantiations (
    id BIGSERIAL PRIMARY KEY,
    benchmark_id BIGINT NOT NULL REFERENCES benchmarks(id) ON DELETE CASCADE,
    abstract_instantiation_id TEXT NOT NULL,
    term TEXT NOT NULL,
    term_hash TEXT NOT NULL,
    axiom_name TEXT NOT NULL,
    bmc_depth INTEGER NOT NULL,
    refinement_step INTEGER NOT NULL,
    in_unsat_core BOOLEAN NOT NULL DEFAULT false,
    UNIQUE (benchmark_id, abstract_instantiation_id)
);

CREATE TABLE IF NOT EXISTS abstract_instantiation_decisions (
    abstract_instantiation_id BIGINT NOT NULL REFERENCES abstract_instantiations(id) ON DELETE CASCADE,
    decision_id BIGINT NOT NULL REFERENCES decisions(id) ON DELETE CASCADE,
    PRIMARY KEY (abstract_instantiation_id, decision_id)
);

CREATE TABLE IF NOT EXISTS indexed_instantiations (
    id BIGSERIAL PRIMARY KEY,
    benchmark_id BIGINT NOT NULL REFERENCES benchmarks(id) ON DELETE CASCADE,
    label TEXT NOT NULL,
    term TEXT NOT NULL,
    term_hash TEXT NOT NULL,
    depth INTEGER NOT NULL,
    unroll_index INTEGER NOT NULL,
    abstract_instantiation_db_id BIGINT REFERENCES abstract_instantiations(id) ON DELETE SET NULL,
    abstract_instantiation_id TEXT,
    in_unsat_core BOOLEAN NOT NULL DEFAULT false,
    UNIQUE (benchmark_id, label)
);

CREATE INDEX IF NOT EXISTS idx_decisions_decision_key ON decisions(decision_key);
CREATE INDEX IF NOT EXISTS idx_abstract_instantiations_benchmark_id ON abstract_instantiations(benchmark_id);
CREATE INDEX IF NOT EXISTS idx_abstract_instantiations_term_hash ON abstract_instantiations(term_hash);
CREATE INDEX IF NOT EXISTS idx_indexed_instantiations_benchmark_id ON indexed_instantiations(benchmark_id);
CREATE INDEX IF NOT EXISTS idx_indexed_instantiations_term_hash ON indexed_instantiations(term_hash);
