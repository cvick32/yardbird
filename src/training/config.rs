//! Configuration for training data logging.

use crate::YardbirdOptions;

/// Configuration for training data logging.
#[derive(Debug, Clone)]
pub struct TrainingConfig {
    /// Whether training logging is enabled
    pub enabled: bool,
    /// Postgres database URL
    pub database_url: Option<String>,
    /// Name of the cost function being used
    pub cost_function_name: String,
}

impl TrainingConfig {
    /// Create a TrainingConfig from YardbirdOptions
    pub fn from_options(options: &YardbirdOptions) -> Self {
        TrainingConfig {
            enabled: options.train,
            database_url: options.database_url.clone(),
            cost_function_name: options.cost_function.to_string(),
        }
    }

    /// Check if training is properly configured (enabled with valid database URL)
    pub fn is_active(&self) -> bool {
        self.enabled && self.database_url.is_some()
    }
}
