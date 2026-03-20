//! Runtime training session orchestration.

use std::time::Instant;

use log::info;

use crate::{training::TrainingLogger, ProofLoopResult, YardbirdOptions};

use super::{NoOpLogger, TrainingConfig};

pub struct TrainingSession {
    logger: Box<dyn TrainingLogger>,
    benchmark_id: i64,
    started_at: Instant,
}

impl std::fmt::Debug for TrainingSession {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TrainingSession")
            .field("benchmark_id", &self.benchmark_id)
            .finish_non_exhaustive()
    }
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
            let mut logger = Box::new(super::PostgresLogger::from_url(&database_url)?)
                as Box<dyn TrainingLogger>;
            let benchmark_id =
                logger.start_benchmark(benchmark_name, &config.cost_function_name)?;
            Ok(Some(Self {
                logger,
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
