//! Runtime training session orchestration.

use std::time::Instant;

use log::info;

use crate::{training::TrainingLogger, ProofLoopResult, YardbirdOptions};

use super::{NoOpLogger, TrainingConfig};

#[cfg(feature = "training")]
use super::TrainingRunRecord;
#[cfg(feature = "training")]
use std::process::Command;
#[cfg(feature = "training")]
use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(feature = "training")]
const TRAINING_SCHEMA_VERSION: &str = "004_training_runs";

pub struct TrainingSession {
    logger: Box<dyn TrainingLogger>,
    training_run_id: i64,
    training_run_version: String,
    benchmark_id: i64,
    started_at: Instant,
}

impl std::fmt::Debug for TrainingSession {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TrainingSession")
            .field("training_run_id", &self.training_run_id)
            .field("training_run_version", &self.training_run_version)
            .field("benchmark_id", &self.benchmark_id)
            .finish_non_exhaustive()
    }
}

#[cfg(feature = "training")]
fn auto_training_run_version() -> String {
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .unwrap_or_default();
    format!("training-run-{timestamp}-pid{}", std::process::id())
}

#[cfg(feature = "training")]
fn git_output(args: &[&str]) -> Option<String> {
    let output = Command::new("git").args(args).output().ok()?;
    if !output.status.success() {
        return None;
    }

    let value = String::from_utf8(output.stdout).ok()?;
    let trimmed = value.trim();
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed.to_string())
    }
}

#[cfg(feature = "training")]
fn git_commit() -> Option<String> {
    git_output(&["rev-parse", "HEAD"])
}

#[cfg(feature = "training")]
fn git_dirty_worktree() -> bool {
    git_output(&["status", "--porcelain"])
        .map(|stdout| !stdout.is_empty())
        .unwrap_or(false)
}

impl TrainingSession {
    pub fn from_options(options: &YardbirdOptions) -> anyhow::Result<Option<Self>> {
        let config = TrainingConfig::from_options(options);
        if !config.enabled {
            return Ok(None);
        }

        #[cfg(not(feature = "training"))]
        {
            let _ = options;
            anyhow::bail!(
                "--train was requested, but yardbird was built without the `training` feature"
            );
        }

        #[cfg(feature = "training")]
        {
            let database_url = config.database_url.clone().ok_or_else(|| {
                anyhow::anyhow!("--train requires --database-url or YARDBIRD_DATABASE_URL")
            })?;
            let benchmark_name = options.require_filename()?;
            let training_run_version = config
                .training_run_version
                .clone()
                .unwrap_or_else(auto_training_run_version);
            let mut logger = Box::new(super::PostgresLogger::from_url(&database_url)?)
                as Box<dyn TrainingLogger>;
            let training_run_id = logger.start_training_run(&TrainingRunRecord {
                run_version: training_run_version.clone(),
                label: None,
                git_commit: git_commit(),
                dirty_worktree: git_dirty_worktree(),
                schema_version: TRAINING_SCHEMA_VERSION.to_string(),
                lab_run_id: None,
            })?;
            let benchmark_id = logger.start_benchmark(
                Some(training_run_id),
                benchmark_name,
                &config.cost_function_name,
            )?;
            Ok(Some(Self {
                logger,
                training_run_id,
                training_run_version,
                benchmark_id,
                started_at: Instant::now(),
            }))
        }
    }

    pub fn complete_result(&mut self, result: &ProofLoopResult) -> anyhow::Result<()> {
        use std::collections::HashMap;

        info!(
            "Persisting training data: {} decisions, {} abstract instantiations, {} indexed instantiations",
            result.decision_data.len(),
            result.abstract_instantiations.len(),
            result.indexed_instantiations.len()
        );

        let mut decision_ids = HashMap::new();
        for decision in &result.decision_data {
            let decision_id = self.logger.log_decision(self.benchmark_id, decision)?;
            decision_ids.insert(decision.decision_key.clone(), decision_id);
        }
        info!("Persisted decision rows");

        let mut abstract_instantiation_ids = HashMap::new();
        for instantiation in &result.abstract_instantiations {
            let abstract_db_id = self
                .logger
                .log_abstract_instantiation(self.benchmark_id, instantiation)?;
            for decision_key in &instantiation.decision_keys {
                if let Some(decision_id) = decision_ids.get(decision_key) {
                    self.logger
                        .link_abstract_instantiation_decision(abstract_db_id, *decision_id)?;
                }
            }
            abstract_instantiation_ids.insert(
                instantiation.abstract_instantiation_id.clone(),
                abstract_db_id,
            );
        }
        info!("Persisted abstract instantiation rows");

        for indexed in &result.indexed_instantiations {
            let abstract_db_id = indexed
                .abstract_instantiation_id
                .as_ref()
                .and_then(|id| abstract_instantiation_ids.get(id).copied());
            self.logger
                .log_indexed_instantiation(self.benchmark_id, indexed, abstract_db_id)?;
        }
        info!("Persisted indexed instantiation rows");

        for unsat_event in &result.unsat_events {
            self.logger
                .log_unsat_event(self.benchmark_id, unsat_event)?;
        }
        info!("Persisted unsat event rows");

        let success = !result.counterexample;
        self.logger.complete_benchmark(
            self.benchmark_id,
            success,
            result.total_refinement_steps,
            self.started_at.elapsed().as_millis() as u64,
            result.unsat_core.as_ref(),
        )?;
        self.logger.flush()?;
        info!("Finished benchmark persistence");
        Ok(())
    }

    pub fn complete_failure(&mut self) -> anyhow::Result<()> {
        self.logger.complete_benchmark(
            self.benchmark_id,
            false,
            0,
            self.started_at.elapsed().as_millis() as u64,
            None,
        )?;
        self.logger.flush()?;
        Ok(())
    }
}

impl Default for TrainingSession {
    fn default() -> Self {
        Self {
            logger: Box::new(NoOpLogger::new()),
            training_run_id: 0,
            training_run_version: "noop-training-run".to_string(),
            benchmark_id: 0,
            started_at: Instant::now(),
        }
    }
}

pub fn reset_training_database(database_url: Option<&str>) -> anyhow::Result<()> {
    #[cfg(not(feature = "training"))]
    {
        let _ = database_url;
        anyhow::bail!(
            "--train-reset was requested, but yardbird was built without the `training` feature"
        );
    }

    #[cfg(feature = "training")]
    {
        let database_url = database_url.ok_or_else(|| {
            anyhow::anyhow!("--train-reset requires --database-url or YARDBIRD_DATABASE_URL")
        })?;
        let runtime = tokio::runtime::Runtime::new()?;
        runtime.block_on(async {
            let db = super::DbConnection::new(database_url).await?;
            db.run_migrations().await?;
            db.reset_training_tables().await?;
            Ok::<(), anyhow::Error>(())
        })?;
        Ok(())
    }
}
