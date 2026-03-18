//! Training data logger trait and implementations.
//!
//! The `TrainingLogger` trait defines the interface for logging training data.
//! When `--train` is not set, the `NoOpLogger` is used which has zero overhead.

use crate::driver::UnsatCoreInfo;

use super::schema::DecisionRecord;

/// Result type for training logger operations.
pub type LoggerResult<T> = Result<T, LoggerError>;

/// Error type for training logger operations.
#[derive(Debug, thiserror::Error)]
pub enum LoggerError {
    #[error("Database error: {0}")]
    Database(String),
    #[error("Configuration error: {0}")]
    Config(String),
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Trait for logging training data.
///
/// This trait allows for different implementations:
/// - `NoOpLogger` for when training is disabled (zero overhead)
/// - `PostgresLogger` for actual database logging
pub trait TrainingLogger: Send {
    /// Start logging a new benchmark.
    ///
    /// Returns a benchmark ID that should be used for subsequent logging calls.
    fn start_benchmark(&mut self, name: &str, cost_fn: &str) -> LoggerResult<i64>;

    /// Log a decision point with candidate terms.
    ///
    /// Returns a decision ID.
    fn log_decision(&mut self, benchmark_id: i64, decision: &DecisionRecord) -> LoggerResult<i64>;

    /// Complete a benchmark with final status and unsat core info.
    fn complete_benchmark(
        &mut self,
        benchmark_id: i64,
        success: bool,
        refinements: u32,
        time_ms: u64,
        core: Option<&UnsatCoreInfo>,
    ) -> LoggerResult<()>;

    /// Flush any buffered data to the database.
    fn flush(&mut self) -> LoggerResult<()>;
}

/// No-op logger that does nothing.
///
/// Used when training is disabled. All methods are inlined and should be
/// optimized away by the compiler.
#[derive(Debug, Default)]
pub struct NoOpLogger;

impl NoOpLogger {
    pub fn new() -> Self {
        NoOpLogger
    }
}

impl TrainingLogger for NoOpLogger {
    #[inline(always)]
    fn start_benchmark(&mut self, _name: &str, _cost_fn: &str) -> LoggerResult<i64> {
        Ok(0)
    }

    #[inline(always)]
    fn log_decision(
        &mut self,
        _benchmark_id: i64,
        _decision: &DecisionRecord,
    ) -> LoggerResult<i64> {
        Ok(0)
    }

    #[inline(always)]
    fn complete_benchmark(
        &mut self,
        _benchmark_id: i64,
        _success: bool,
        _refinements: u32,
        _time_ms: u64,
        _core: Option<&UnsatCoreInfo>,
    ) -> LoggerResult<()> {
        Ok(())
    }

    #[inline(always)]
    fn flush(&mut self) -> LoggerResult<()> {
        Ok(())
    }
}

// PostgresLogger is only available when the training feature is enabled
#[cfg(feature = "training")]
mod postgres_impl {
    use super::*;
    use crate::training::db::DbConnection;
    use log::info;

    /// Logger that writes training data to a Postgres database.
    pub struct PostgresLogger {
        db: DbConnection,
        /// Buffer for decisions to batch insert
        decision_buffer: Vec<(i64, DecisionRecord)>,
        /// Number of decisions to buffer before flushing
        buffer_size: usize,
    }

    impl PostgresLogger {
        /// Create a new PostgresLogger with the given database connection.
        pub fn new(db: DbConnection) -> Self {
            PostgresLogger {
                db,
                decision_buffer: Vec::new(),
                buffer_size: 100, // Flush every 100 decisions
            }
        }

        /// Create a PostgresLogger from a database URL.
        pub async fn from_url(database_url: &str) -> LoggerResult<Self> {
            let db = DbConnection::new(database_url).await.map_err(|e| {
                LoggerError::Database(format!("Failed to connect to database: {}", e))
            })?;
            Ok(PostgresLogger::new(db))
        }

        /// Flush buffered decisions to the database.
        async fn flush_buffer(&mut self) -> LoggerResult<()> {
            if self.decision_buffer.is_empty() {
                return Ok(());
            }

            for (benchmark_id, decision) in self.decision_buffer.drain(..) {
                self.db
                    .insert_decision(benchmark_id, &decision)
                    .await
                    .map_err(|e| LoggerError::Database(e.to_string()))?;
            }

            Ok(())
        }
    }

    impl TrainingLogger for PostgresLogger {
        fn start_benchmark(&mut self, name: &str, cost_fn: &str) -> LoggerResult<i64> {
            info!(
                "Starting benchmark logging: {} with cost function {}",
                name, cost_fn
            );

            // Use tokio runtime to run async code
            let rt = tokio::runtime::Handle::current();
            rt.block_on(async {
                self.db
                    .insert_benchmark(name, cost_fn)
                    .await
                    .map_err(|e| LoggerError::Database(e.to_string()))
            })
        }

        fn log_decision(
            &mut self,
            benchmark_id: i64,
            decision: &DecisionRecord,
        ) -> LoggerResult<i64> {
            self.decision_buffer.push((benchmark_id, decision.clone()));

            if self.decision_buffer.len() >= self.buffer_size {
                let rt = tokio::runtime::Handle::current();
                rt.block_on(self.flush_buffer())?;
            }

            // Return a placeholder ID since we're buffering
            Ok(self.decision_buffer.len() as i64)
        }

        fn complete_benchmark(
            &mut self,
            benchmark_id: i64,
            success: bool,
            refinements: u32,
            time_ms: u64,
            core: Option<&UnsatCoreInfo>,
        ) -> LoggerResult<()> {
            let rt = tokio::runtime::Handle::current();
            rt.block_on(async {
                // Flush any remaining buffered decisions
                self.flush_buffer().await?;

                // Update benchmark status
                self.db
                    .complete_benchmark(benchmark_id, success, refinements, time_ms)
                    .await
                    .map_err(|e| LoggerError::Database(e.to_string()))?;

                // Insert core appearances if we have unsat core info
                if let Some(core_info) = core {
                    for inst in &core_info.core_instantiations {
                        let term_hash =
                            crate::training::canonical_term_hash_from_string(&inst.term);
                        self.db
                            .insert_core_appearance(benchmark_id, &term_hash)
                            .await
                            .map_err(|e| LoggerError::Database(e.to_string()))?;
                    }
                }

                Ok(())
            })
        }

        fn flush(&mut self) -> LoggerResult<()> {
            let rt = tokio::runtime::Handle::current();
            rt.block_on(self.flush_buffer())
        }
    }
}

#[cfg(feature = "training")]
pub use postgres_impl::PostgresLogger;
