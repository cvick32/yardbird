-- Unsat-event logging schema additions.

CREATE TABLE IF NOT EXISTS unsat_events (
    id BIGSERIAL PRIMARY KEY,
    benchmark_id BIGINT NOT NULL REFERENCES benchmarks(id) ON DELETE CASCADE,
    event_index INTEGER NOT NULL,
    bmc_depth INTEGER,
    global_refinement_step INTEGER,
    check_sat_index INTEGER,
    total_instantiations_added BIGINT NOT NULL,
    instantiations_since_last_unsat BIGINT NOT NULL,
    core_size INTEGER,
    conflicts DOUBLE PRECISION,
    decisions DOUBLE PRECISION,
    restarts DOUBLE PRECISION,
    propagations DOUBLE PRECISION,
    array_ax1 DOUBLE PRECISION,
    array_ax2 DOUBLE PRECISION,
    array_ext_ax DOUBLE PRECISION,
    solver_stats_snapshot JSONB NOT NULL,
    solver_stats_delta JSONB NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    UNIQUE (benchmark_id, event_index)
);

CREATE INDEX IF NOT EXISTS idx_unsat_events_benchmark_id ON unsat_events(benchmark_id);
CREATE INDEX IF NOT EXISTS idx_unsat_events_refinement_step ON unsat_events(global_refinement_step);
CREATE INDEX IF NOT EXISTS idx_unsat_events_check_sat_index ON unsat_events(check_sat_index);
