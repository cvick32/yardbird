-- Training run grouping for versioned data collection campaigns.

CREATE TABLE IF NOT EXISTS training_runs (
    id BIGSERIAL PRIMARY KEY,
    run_version TEXT NOT NULL UNIQUE,
    label TEXT,
    git_commit TEXT,
    dirty_worktree BOOLEAN NOT NULL DEFAULT false,
    schema_version TEXT,
    lab_run_id TEXT,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

ALTER TABLE benchmarks
ADD COLUMN IF NOT EXISTS training_run_id BIGINT
REFERENCES training_runs(id) ON DELETE SET NULL;

CREATE INDEX IF NOT EXISTS idx_benchmarks_training_run_id
ON benchmarks(training_run_id);
