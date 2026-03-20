//! Training data logger trait and implementations.
//!
//! The `TrainingLogger` trait defines the interface for logging training data.
//! When `--train` is not set, the `NoOpLogger` is used which has zero overhead.

use crate::driver::UnsatCoreInfo;

use super::schema::{AbstractInstantiationRecord, DecisionRecord, IndexedInstantiationRecord};

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
    fn set_decision_key(&mut self, decision_id: i64, decision_key: &str) -> LoggerResult<()>;

    /// Log an original abstract instantiation.
    fn log_abstract_instantiation(
        &mut self,
        benchmark_id: i64,
        instantiation: &AbstractInstantiationRecord,
    ) -> LoggerResult<i64>;

    /// Link an abstract instantiation back to a decision row.
    fn link_abstract_instantiation_decision(
        &mut self,
        abstract_instantiation_id: i64,
        decision_id: i64,
    ) -> LoggerResult<()>;

    /// Log an indexed solver assertion that came from an abstract instantiation.
    fn log_indexed_instantiation(
        &mut self,
        benchmark_id: i64,
        instantiation: &IndexedInstantiationRecord,
        abstract_instantiation_id: Option<i64>,
    ) -> LoggerResult<()>;

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
    fn set_decision_key(&mut self, _decision_id: i64, _decision_key: &str) -> LoggerResult<()> {
        Ok(())
    }

    #[inline(always)]
    fn log_abstract_instantiation(
        &mut self,
        _benchmark_id: i64,
        _instantiation: &AbstractInstantiationRecord,
    ) -> LoggerResult<i64> {
        Ok(0)
    }

    #[inline(always)]
    fn link_abstract_instantiation_decision(
        &mut self,
        _abstract_instantiation_id: i64,
        _decision_id: i64,
    ) -> LoggerResult<()> {
        Ok(())
    }

    #[inline(always)]
    fn log_indexed_instantiation(
        &mut self,
        _benchmark_id: i64,
        _instantiation: &IndexedInstantiationRecord,
        _abstract_instantiation_id: Option<i64>,
    ) -> LoggerResult<()> {
        Ok(())
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
        runtime: tokio::runtime::Runtime,
        /// Buffer for decisions to batch insert
        decision_buffer: Vec<(i64, DecisionRecord)>,
    }

    impl PostgresLogger {
        /// Create a PostgresLogger from a database URL.
        pub fn from_url(database_url: &str) -> LoggerResult<Self> {
            let runtime = tokio::runtime::Runtime::new()
                .map_err(|e| LoggerError::Config(format!("Failed to create runtime: {}", e)))?;
            let db = runtime.block_on(async {
                let db = DbConnection::new(database_url).await.map_err(|e| {
                    LoggerError::Database(format!("Failed to connect to database: {}", e))
                })?;
                db.run_migrations().await.map_err(|e| {
                    LoggerError::Database(format!("Failed to run migrations: {}", e))
                })?;
                Ok::<DbConnection, LoggerError>(db)
            })?;

            Ok(PostgresLogger {
                db,
                runtime,
                decision_buffer: Vec::new(),
            })
        }

        /// Flush buffered decisions to the database.
        fn flush_buffer(&mut self) -> LoggerResult<()> {
            if self.decision_buffer.is_empty() {
                return Ok(());
            }

            let pending = std::mem::take(&mut self.decision_buffer);
            let db = &self.db;
            self.runtime.block_on(async {
                for (benchmark_id, decision) in pending {
                    db.insert_decision(benchmark_id, &decision)
                        .await
                        .map_err(|e| LoggerError::Database(e.to_string()))?;
                }

                Ok(())
            })
        }
    }

    impl TrainingLogger for PostgresLogger {
        fn start_benchmark(&mut self, name: &str, cost_fn: &str) -> LoggerResult<i64> {
            info!(
                "Starting benchmark logging: {} with cost function {}",
                name, cost_fn
            );

            let db = &self.db;
            self.runtime.block_on(async {
                db.insert_benchmark(name, cost_fn)
                    .await
                    .map_err(|e| LoggerError::Database(e.to_string()))
            })
        }

        fn log_decision(
            &mut self,
            benchmark_id: i64,
            decision: &DecisionRecord,
        ) -> LoggerResult<i64> {
            let db = &self.db;
            self.runtime.block_on(async {
                db.insert_decision(benchmark_id, decision)
                    .await
                    .map_err(|e| LoggerError::Database(e.to_string()))
            })
        }

        fn set_decision_key(&mut self, decision_id: i64, decision_key: &str) -> LoggerResult<()> {
            let db = &self.db;
            self.runtime.block_on(async {
                db.set_decision_key(decision_id, decision_key)
                    .await
                    .map_err(|e| LoggerError::Database(e.to_string()))
            })
        }

        fn log_abstract_instantiation(
            &mut self,
            benchmark_id: i64,
            instantiation: &AbstractInstantiationRecord,
        ) -> LoggerResult<i64> {
            let db = &self.db;
            self.runtime.block_on(async {
                db.insert_abstract_instantiation(benchmark_id, instantiation)
                    .await
                    .map_err(|e| LoggerError::Database(e.to_string()))
            })
        }

        fn link_abstract_instantiation_decision(
            &mut self,
            abstract_instantiation_id: i64,
            decision_id: i64,
        ) -> LoggerResult<()> {
            let db = &self.db;
            self.runtime.block_on(async {
                db.link_abstract_instantiation_decision(abstract_instantiation_id, decision_id)
                    .await
                    .map_err(|e| LoggerError::Database(e.to_string()))
            })
        }

        fn log_indexed_instantiation(
            &mut self,
            benchmark_id: i64,
            instantiation: &IndexedInstantiationRecord,
            abstract_instantiation_id: Option<i64>,
        ) -> LoggerResult<()> {
            let db = &self.db;
            self.runtime.block_on(async {
                db.insert_indexed_instantiation(
                    benchmark_id,
                    instantiation,
                    abstract_instantiation_id,
                )
                .await
                .map_err(|e| LoggerError::Database(e.to_string()))
            })
        }

        fn complete_benchmark(
            &mut self,
            benchmark_id: i64,
            success: bool,
            refinements: u32,
            time_ms: u64,
            core: Option<&UnsatCoreInfo>,
        ) -> LoggerResult<()> {
            self.flush_buffer()?;

            let db = &self.db;
            self.runtime.block_on(async {
                db.complete_benchmark(benchmark_id, success, refinements, time_ms)
                    .await
                    .map_err(|e| LoggerError::Database(e.to_string()))?;

                // Insert core appearances if we have unsat core info
                if let Some(core_info) = core {
                    for inst in &core_info.core_instantiations {
                        let term_hash =
                            crate::training::canonical_term_hash_from_string(&inst.term);
                        db.insert_core_appearance(benchmark_id, &term_hash)
                            .await
                            .map_err(|e| LoggerError::Database(e.to_string()))?;
                    }
                }

                Ok(())
            })
        }

        fn flush(&mut self) -> LoggerResult<()> {
            self.flush_buffer()
        }
    }
}

#[cfg(feature = "training")]
pub use postgres_impl::PostgresLogger;
