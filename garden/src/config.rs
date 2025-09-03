use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use yardbird::{CostFunction, Strategy};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalConfig {
    pub examples_dir: PathBuf,
    pub timeout_seconds: u64,
    pub retry_count: usize,
    pub output_format: String,
    pub include_patterns: Vec<String>,
    pub exclude_patterns: Vec<String>,
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            examples_dir: PathBuf::from("examples"),
            timeout_seconds: 30,
            retry_count: 2,
            output_format: "json".to_string(),
            include_patterns: vec![],
            exclude_patterns: vec![],
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParameterMatrix {
    pub depths: Vec<u16>,
    pub strategies: Vec<Strategy>,
    pub cost_functions: Vec<CostFunction>,
    #[serde(default)]
    pub timeout_seconds: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IndividualConfig {
    pub name: String,
    pub depth: u16,
    pub strategy: Strategy,
    pub cost_function: CostFunction,
    #[serde(default)]
    pub timeout_seconds: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OutputConfig {
    pub include_metadata: bool,
    pub pretty_json: bool,
    pub timestamp_format: String,
}

impl Default for OutputConfig {
    fn default() -> Self {
        Self {
            include_metadata: true,
            pretty_json: true,
            timestamp_format: "%Y%m%d_%H%M%S".to_string(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CloudConfig {
    pub instance_type: String,
    pub region: String,
    pub s3_bucket: String,
    pub auto_teardown: bool,
}

impl Default for CloudConfig {
    fn default() -> Self {
        Self {
            instance_type: "c5.xlarge".to_string(),
            region: "us-west-2".to_string(),
            s3_bucket: "yardbird-benchmarks".to_string(),
            auto_teardown: true,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkConfig {
    #[serde(default)]
    pub global: GlobalConfig,
    #[serde(default)]
    pub parameter_matrices: std::collections::HashMap<String, ParameterMatrix>,
    #[serde(default)]
    pub individual_configs: Vec<IndividualConfig>,
    #[serde(default)]
    pub output: OutputConfig,
    #[serde(default)]
    pub cloud: CloudConfig,
}

#[derive(Debug, Clone)]
pub struct BenchmarkRun {
    pub name: String,
    pub depth: u16,
    pub strategy: Strategy,
    pub cost_function: CostFunction,
    pub timeout_seconds: u64,
}

impl BenchmarkConfig {
    pub fn from_file(path: &PathBuf) -> Result<Self> {
        let content = std::fs::read_to_string(path)
            .with_context(|| format!("Failed to read config file: {}", path.display()))?;
        
        serde_yaml::from_str(&content)
            .with_context(|| format!("Failed to parse config file: {}", path.display()))
    }

    pub fn generate_benchmark_runs(&self, matrix_name: Option<&str>) -> Result<Vec<BenchmarkRun>> {
        let mut runs = Vec::new();

        // Add individual configs
        for config in &self.individual_configs {
            runs.push(BenchmarkRun {
                name: config.name.clone(),
                depth: config.depth,
                strategy: config.strategy,
                cost_function: config.cost_function,
                timeout_seconds: config.timeout_seconds.unwrap_or(self.global.timeout_seconds),
            });
        }

        // Add matrix configs
        if let Some(matrix_name) = matrix_name {
            if let Some(matrix) = self.parameter_matrices.get(matrix_name) {
                for &depth in &matrix.depths {
                    for &strategy in &matrix.strategies {
                        for &cost_function in &matrix.cost_functions {
                            runs.push(BenchmarkRun {
                                name: format!("{}_d{}_s{:?}_c{:?}", matrix_name, depth, strategy, cost_function),
                                depth,
                                strategy,
                                cost_function,
                                timeout_seconds: matrix.timeout_seconds.unwrap_or(self.global.timeout_seconds),
                            });
                        }
                    }
                }
            }
        } else {
            // Generate all matrices if none specified
            for (matrix_name, matrix) in &self.parameter_matrices {
                for &depth in &matrix.depths {
                    for &strategy in &matrix.strategies {
                        for &cost_function in &matrix.cost_functions {
                            runs.push(BenchmarkRun {
                                name: format!("{}_d{}_s{:?}_c{:?}", matrix_name, depth, strategy, cost_function),
                                depth,
                                strategy,
                                cost_function,
                                timeout_seconds: matrix.timeout_seconds.unwrap_or(self.global.timeout_seconds),
                            });
                        }
                    }
                }
            }
        }

        Ok(runs)
    }
}