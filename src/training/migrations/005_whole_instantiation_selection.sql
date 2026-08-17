-- Preserve every complete candidate considered by whole-instantiation ranking.

ALTER TABLE abstract_instantiations
ADD COLUMN IF NOT EXISTS was_selected BOOLEAN NOT NULL DEFAULT true;

CREATE INDEX IF NOT EXISTS idx_abstract_instantiations_selected
ON abstract_instantiations(benchmark_id, was_selected);
