//! Database connection and operations for training data logging.
//!
//! This module is only available when the `training` feature is enabled.

use sqlx::{postgres::PgPoolOptions, PgPool, Row};

use super::schema::DecisionRecord;

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
            INSERT INTO decisions (benchmark_id, bmc_depth, axiom_name, slot_index)
            VALUES ($1, $2, $3, $4)
            RETURNING id
            "#,
        )
        .bind(benchmark_id)
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
        sqlx::query(include_str!("migrations/001_initial.sql"))
            .execute(&self.pool)
            .await?;
        Ok(())
    }
}
