//! Database connection and operations for training data logging.
//!
//! This module is only available when the `training` feature is enabled.

use sqlx::{postgres::PgPoolOptions, PgPool, Row};

use super::schema::{
    AbstractInstantiationRecord, DecisionRecord, IndexedInstantiationRecord, UnsatEventRecord,
};

/// Database connection wrapper with connection pooling.
pub struct DbConnection {
    pool: PgPool,
}

impl DbConnection {
    /// Create a new database connection from a URL.
    pub async fn new(database_url: &str) -> Result<Self, sqlx::Error> {
        let pool = PgPoolOptions::new()
            .max_connections(5)
            .connect(database_url)
            .await?;

        Ok(DbConnection { pool })
    }

    /// Insert a new benchmark and return its ID.
    pub async fn insert_benchmark(&self, name: &str, cost_fn: &str) -> Result<i64, sqlx::Error> {
        let row = sqlx::query(
            r#"
            INSERT INTO benchmarks (name, cost_function, success, total_refinements, total_time_ms)
            VALUES ($1, $2, NULL, NULL, NULL)
            RETURNING id
            "#,
        )
        .bind(name)
        .bind(cost_fn)
        .fetch_one(&self.pool)
        .await?;

        Ok(row.get("id"))
    }

    /// Insert a decision and its candidates.
    pub async fn insert_decision(
        &self,
        benchmark_id: i64,
        decision: &DecisionRecord,
    ) -> Result<i64, sqlx::Error> {
        // Start a transaction
        let mut tx = self.pool.begin().await?;

        // Insert the decision
        let row = sqlx::query(
            r#"
            INSERT INTO decisions (benchmark_id, decision_key, bmc_depth, axiom_name, slot_index)
            VALUES ($1, $2, $3, $4, $5)
            RETURNING id
            "#,
        )
        .bind(benchmark_id)
        .bind(&decision.decision_key)
        .bind(decision.bmc_depth as i32)
        .bind(&decision.axiom_name)
        .bind(decision.slot_index as i32)
        .fetch_one(&mut *tx)
        .await?;

        let decision_id: i64 = row.get("id");

        // Insert all candidates
        for candidate in &decision.candidates {
            sqlx::query(
                r#"
                INSERT INTO candidates (
                    term, decision_id, term_hash, is_constant, is_variable,
                    in_property_vocab, in_transition_vocab, frame_index,
                    ast_size, current_cost, was_chosen
                )
                VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11)
                "#,
            )
            .bind(&candidate.term)
            .bind(decision_id)
            .bind(&candidate.term_hash)
            .bind(candidate.is_constant)
            .bind(candidate.is_variable)
            .bind(candidate.in_property_vocab)
            .bind(candidate.in_transition_vocab)
            .bind(candidate.frame_index)
            .bind(candidate.ast_size)
            .bind(candidate.current_cost)
            .bind(candidate.was_chosen)
            .execute(&mut *tx)
            .await?;
        }

        // Commit the transaction
        tx.commit().await?;

        Ok(decision_id)
    }

    /// Add a stable decision key after the row exists. This keeps migration logic simple.
    pub async fn set_decision_key(
        &self,
        decision_id: i64,
        decision_key: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            r#"
            UPDATE decisions
            SET decision_key = $2
            WHERE id = $1
            "#,
        )
        .bind(decision_id)
        .bind(decision_key)
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    pub async fn insert_abstract_instantiation(
        &self,
        benchmark_id: i64,
        record: &AbstractInstantiationRecord,
    ) -> Result<i64, sqlx::Error> {
        let row = sqlx::query(
            r#"
            INSERT INTO abstract_instantiations (
                benchmark_id, abstract_instantiation_id, term, term_hash,
                axiom_name, bmc_depth, refinement_step, in_unsat_core
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8)
            RETURNING id
            "#,
        )
        .bind(benchmark_id)
        .bind(&record.abstract_instantiation_id)
        .bind(&record.term)
        .bind(&record.term_hash)
        .bind(&record.axiom_name)
        .bind(record.bmc_depth as i32)
        .bind(record.refinement_step as i32)
        .bind(record.in_unsat_core)
        .fetch_one(&self.pool)
        .await?;

        Ok(row.get("id"))
    }

    pub async fn link_abstract_instantiation_decision(
        &self,
        abstract_instantiation_db_id: i64,
        decision_id: i64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            r#"
            INSERT INTO abstract_instantiation_decisions (abstract_instantiation_id, decision_id)
            VALUES ($1, $2)
            ON CONFLICT DO NOTHING
            "#,
        )
        .bind(abstract_instantiation_db_id)
        .bind(decision_id)
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    pub async fn insert_indexed_instantiation(
        &self,
        benchmark_id: i64,
        record: &IndexedInstantiationRecord,
        abstract_instantiation_db_id: Option<i64>,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            r#"
            INSERT INTO indexed_instantiations (
                benchmark_id, label, term, term_hash, depth, unroll_index,
                abstract_instantiation_db_id, abstract_instantiation_id, in_unsat_core
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
            ON CONFLICT (benchmark_id, label) DO NOTHING
            "#,
        )
        .bind(benchmark_id)
        .bind(&record.label)
        .bind(&record.term)
        .bind(&record.term_hash)
        .bind(record.depth as i32)
        .bind(record.unroll_index as i32)
        .bind(abstract_instantiation_db_id)
        .bind(&record.abstract_instantiation_id)
        .bind(record.in_unsat_core)
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    pub async fn insert_unsat_event(
        &self,
        benchmark_id: i64,
        record: &UnsatEventRecord,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            r#"
            INSERT INTO unsat_events (
                benchmark_id, event_index, bmc_depth, global_refinement_step, check_sat_index,
                total_instantiations_added, instantiations_since_last_unsat, core_size,
                conflicts, decisions, restarts, propagations,
                array_ax1, array_ax2, array_ext_ax,
                solver_stats_snapshot, solver_stats_delta
            )
            VALUES (
                $1, $2, $3, $4, $5,
                $6, $7, $8,
                $9, $10, $11, $12,
                $13, $14, $15,
                $16, $17
            )
            ON CONFLICT (benchmark_id, event_index) DO NOTHING
            "#,
        )
        .bind(benchmark_id)
        .bind(record.event_index as i32)
        .bind(record.bmc_depth.map(i32::from))
        .bind(record.global_refinement_step.map(|step| step as i32))
        .bind(record.check_sat_index.map(|index| index as i32))
        .bind(record.total_instantiations_added as i64)
        .bind(record.instantiations_since_last_unsat as i64)
        .bind(record.core_size.map(|size| size as i32))
        .bind(record.conflicts)
        .bind(record.decisions)
        .bind(record.restarts)
        .bind(record.propagations)
        .bind(record.array_ax1)
        .bind(record.array_ax2)
        .bind(record.array_ext_ax)
        .bind(sqlx::types::Json(record.solver_stats_snapshot.clone()))
        .bind(sqlx::types::Json(record.solver_stats_delta.clone()))
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    /// Update a benchmark with completion status.
    pub async fn complete_benchmark(
        &self,
        benchmark_id: i64,
        success: bool,
        refinements: u32,
        time_ms: u64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            r#"
            UPDATE benchmarks
            SET success = $2, total_refinements = $3, total_time_ms = $4
            WHERE id = $1
            "#,
        )
        .bind(benchmark_id)
        .bind(success)
        .bind(refinements as i32)
        .bind(time_ms as i64)
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    /// Insert or update a core appearance.
    pub async fn insert_core_appearance(
        &self,
        benchmark_id: i64,
        term_hash: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            r#"
            INSERT INTO core_appearances (benchmark_id, term_hash, appearance_count)
            VALUES ($1, $2, 1)
            ON CONFLICT (benchmark_id, term_hash)
            DO UPDATE SET appearance_count = core_appearances.appearance_count + 1
            "#,
        )
        .bind(benchmark_id)
        .bind(term_hash)
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    /// Run the database migrations.
    pub async fn run_migrations(&self) -> Result<(), sqlx::Error> {
        sqlx::raw_sql(include_str!("migrations/001_initial.sql"))
            .execute(&self.pool)
            .await?;
        sqlx::raw_sql(include_str!("migrations/002_instantiation_provenance.sql"))
            .execute(&self.pool)
            .await?;
        sqlx::raw_sql(include_str!("migrations/003_unsat_events.sql"))
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    /// Clear all training tables while preserving the schema.
    pub async fn reset_training_tables(&self) -> Result<(), sqlx::Error> {
        sqlx::query(
            r#"
            TRUNCATE TABLE
                indexed_instantiations,
                unsat_events,
                abstract_instantiation_decisions,
                abstract_instantiations,
                core_appearances,
                candidates,
                decisions,
                benchmarks
            RESTART IDENTITY CASCADE
            "#,
        )
        .execute(&self.pool)
        .await?;
        Ok(())
    }
}
