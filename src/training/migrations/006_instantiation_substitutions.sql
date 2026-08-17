-- Carry complete substitutions and post-materialization outcomes through training data.

ALTER TABLE abstract_instantiations
ADD COLUMN IF NOT EXISTS substitution JSONB NOT NULL DEFAULT '[]'::jsonb,
ADD COLUMN IF NOT EXISTS indexed_assertions_attempted BIGINT NOT NULL DEFAULT 0,
ADD COLUMN IF NOT EXISTS indexed_assertions_added BIGINT NOT NULL DEFAULT 0,
ADD COLUMN IF NOT EXISTS indexed_assertions_deduplicated BIGINT NOT NULL DEFAULT 0,
ADD COLUMN IF NOT EXISTS helper_assertions_attempted BIGINT NOT NULL DEFAULT 0,
ADD COLUMN IF NOT EXISTS helper_assertions_added BIGINT NOT NULL DEFAULT 0,
ADD COLUMN IF NOT EXISTS helper_assertions_deduplicated BIGINT NOT NULL DEFAULT 0;

ALTER TABLE indexed_instantiations
ADD COLUMN IF NOT EXISTS frame INTEGER NOT NULL DEFAULT 0,
ADD COLUMN IF NOT EXISTS substitution JSONB NOT NULL DEFAULT '[]'::jsonb;
