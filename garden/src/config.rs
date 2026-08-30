use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use yardbird::{
    CostFunction, EGraphBuilderStrategy, InstantiationRankerStrategy, SolverBackend, Strategy,
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalConfig {
    pub examples_dir: PathBuf,
    pub timeout_seconds: u64,
    pub retry_count: usize,
    #[serde(default = "default_jobs")]
    pub jobs: usize,
    #[serde(default)]
    pub benchmark_limit: Option<usize>,
    #[serde(default = "default_sample_seed")]
    pub sample_seed: u64,
    #[serde(default)]
    pub require_array_reads_and_writes: bool,
    pub output_format: String,
    pub include_patterns: Vec<String>,
    pub exclude_patterns: Vec<String>,
}

fn default_jobs() -> usize {
    1
}

fn default_sample_seed() -> u64 {
    0
}

impl Default for GlobalConfig {
    fn default() -> Self {
        Self {
            examples_dir: PathBuf::from("examples"),
            timeout_seconds: 30,
            retry_count: 2,
            jobs: default_jobs(),
            benchmark_limit: None,
            sample_seed: default_sample_seed(),
            require_array_reads_and_writes: false,
            output_format: "json".to_string(),
            include_patterns: vec![],
            exclude_patterns: vec![],
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParameterMatrix {
    pub depths: Vec<u16>,
    #[serde(default = "default_solvers")]
    pub solvers: Vec<SolverBackend>,
    pub strategies: Vec<Strategy>,
    pub cost_functions: Vec<CostFunction>,
    #[serde(default = "default_egraph_builders")]
    pub egraph_builders: Vec<EGraphBuilderStrategy>,
    #[serde(default = "default_instantiation_rankers")]
    pub instantiation_rankers: Vec<InstantiationRankerStrategy>,
    #[serde(default)]
    pub preprocess_exact_read_after_write: bool,
    #[serde(default)]
    pub timeout_seconds: Option<u64>,
}

fn default_solver() -> SolverBackend {
    SolverBackend::Z3
}

fn default_solvers() -> Vec<SolverBackend> {
    vec![SolverBackend::Z3]
}

fn default_egraph_builder() -> EGraphBuilderStrategy {
    EGraphBuilderStrategy::SourceThenFull
}

fn default_egraph_builders() -> Vec<EGraphBuilderStrategy> {
    vec![default_egraph_builder()]
}

fn default_instantiation_ranker() -> InstantiationRankerStrategy {
    InstantiationRankerStrategy::PreferSource
}

fn default_instantiation_rankers() -> Vec<InstantiationRankerStrategy> {
    vec![default_instantiation_ranker()]
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IndividualConfig {
    pub name: String,
    pub depth: u16,
    #[serde(default = "default_solver")]
    pub solver: SolverBackend,
    pub strategy: Strategy,
    pub cost_function: CostFunction,
    #[serde(default = "default_egraph_builder")]
    pub egraph_builder: EGraphBuilderStrategy,
    #[serde(default = "default_instantiation_ranker")]
    pub instantiation_ranker: InstantiationRankerStrategy,
    #[serde(default)]
    pub preprocess_exact_read_after_write: bool,
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
    pub solver: SolverBackend,
    pub strategy: Strategy,
    pub cost_function: CostFunction,
    pub egraph_builder: EGraphBuilderStrategy,
    pub instantiation_ranker: InstantiationRankerStrategy,
    pub preprocess_exact_read_after_write: bool,
    pub timeout_seconds: u64,
}

fn matrix_run_name(
    matrix_name: &str,
    depth: u16,
    solver: SolverBackend,
    strategy: Strategy,
    cost_function: CostFunction,
    selection: (EGraphBuilderStrategy, InstantiationRankerStrategy),
    preprocess_exact_read_after_write: bool,
) -> String {
    let (egraph_builder, instantiation_ranker) = selection;
    let base = format!(
        "{}_d{}_solver{:?}_s{:?}_c{:?}",
        matrix_name, depth, solver, strategy, cost_function
    );
    let name = match egraph_builder {
        EGraphBuilderStrategy::Full => base,
        EGraphBuilderStrategy::SourceThenFull | EGraphBuilderStrategy::ConeThenFull => {
            format!("{base}_e{egraph_builder:?}")
        }
    };
    let name = match instantiation_ranker {
        InstantiationRankerStrategy::PreferSource => name,
        InstantiationRankerStrategy::TermCost => format!("{name}_r{instantiation_ranker:?}"),
    };
    if preprocess_exact_read_after_write {
        format!("{name}_preprocessExactReadAfterWrite")
    } else {
        name
    }
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

        if let Some(matrix_name) = matrix_name {
            let matrix = self
                .parameter_matrices
                .get(matrix_name)
                .with_context(|| format!("Unknown parameter matrix: {matrix_name}"))?;
            runs.extend(self.generate_matrix_runs(matrix_name, matrix));
        } else {
            for config in &self.individual_configs {
                runs.push(BenchmarkRun {
                    name: config.name.clone(),
                    depth: config.depth,
                    solver: config.solver,
                    strategy: config.strategy,
                    cost_function: config.cost_function,
                    egraph_builder: config.egraph_builder,
                    instantiation_ranker: config.instantiation_ranker,
                    preprocess_exact_read_after_write: config.preprocess_exact_read_after_write,
                    timeout_seconds: config
                        .timeout_seconds
                        .unwrap_or(self.global.timeout_seconds),
                });
            }

            for (matrix_name, matrix) in &self.parameter_matrices {
                runs.extend(self.generate_matrix_runs(matrix_name, matrix));
            }
        }

        Ok(runs)
    }

    fn generate_matrix_runs(
        &self,
        matrix_name: &str,
        matrix: &ParameterMatrix,
    ) -> Vec<BenchmarkRun> {
        let mut runs = Vec::new();
        for &depth in &matrix.depths {
            for &solver in &matrix.solvers {
                for &strategy in &matrix.strategies {
                    for &cost_function in &matrix.cost_functions {
                        for &egraph_builder in &matrix.egraph_builders {
                            for &instantiation_ranker in &matrix.instantiation_rankers {
                                runs.push(BenchmarkRun {
                                    name: matrix_run_name(
                                        matrix_name,
                                        depth,
                                        solver,
                                        strategy,
                                        cost_function,
                                        (egraph_builder, instantiation_ranker),
                                        matrix.preprocess_exact_read_after_write,
                                    ),
                                    depth,
                                    solver,
                                    strategy,
                                    cost_function,
                                    egraph_builder,
                                    instantiation_ranker,
                                    preprocess_exact_read_after_write: matrix
                                        .preprocess_exact_read_after_write,
                                    timeout_seconds: matrix
                                        .timeout_seconds
                                        .unwrap_or(self.global.timeout_seconds),
                                });
                            }
                        }
                    }
                }
            }
        }
        runs
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::{matrix_run_name, BenchmarkConfig};
    use yardbird::{
        CostFunction, EGraphBuilderStrategy, InstantiationRankerStrategy, SolverBackend, Strategy,
    };

    #[test]
    fn older_global_configs_receive_sampling_defaults() {
        let config: BenchmarkConfig = serde_yaml::from_str(
            r#"
global:
  examples_dir: examples/array
  timeout_seconds: 30
  retry_count: 1
  output_format: json
  include_patterns: []
  exclude_patterns: []
"#,
        )
        .expect("legacy config should still parse");

        assert_eq!(config.global.jobs, 1);
        assert_eq!(config.global.benchmark_limit, None);
        assert_eq!(config.global.sample_seed, 0);
        assert!(!config.global.require_array_reads_and_writes);
    }

    #[test]
    fn full_builder_preserves_existing_run_names() {
        let full = matrix_run_name(
            "deep",
            50,
            SolverBackend::Z3,
            Strategy::Abstract,
            CostFunction::BmcCost,
            (
                EGraphBuilderStrategy::Full,
                InstantiationRankerStrategy::PreferSource,
            ),
            false,
        );
        let cone = matrix_run_name(
            "deep",
            50,
            SolverBackend::Z3,
            Strategy::Abstract,
            CostFunction::BmcCost,
            (
                EGraphBuilderStrategy::ConeThenFull,
                InstantiationRankerStrategy::PreferSource,
            ),
            false,
        );
        let source = matrix_run_name(
            "deep",
            50,
            SolverBackend::Z3,
            Strategy::Abstract,
            CostFunction::BmcCost,
            (
                EGraphBuilderStrategy::SourceThenFull,
                InstantiationRankerStrategy::PreferSource,
            ),
            false,
        );

        assert_eq!(full, "deep_d50_solverZ3_sAbstract_cBmcCost");
        assert_eq!(
            source,
            "deep_d50_solverZ3_sAbstract_cBmcCost_eSourceThenFull"
        );
        assert_eq!(cone, "deep_d50_solverZ3_sAbstract_cBmcCost_eConeThenFull");
    }

    #[test]
    fn preprocessing_is_explicit_in_run_names() {
        let name = matrix_run_name(
            "formula",
            50,
            SolverBackend::Z3,
            Strategy::Abstract,
            CostFunction::BmcCost,
            (
                EGraphBuilderStrategy::ConeThenFull,
                InstantiationRankerStrategy::PreferSource,
            ),
            true,
        );

        assert!(name.ends_with("_preprocessExactReadAfterWrite"));
    }

    #[test]
    fn formula_transformation_matrix_enables_preprocessing() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benchmark_config.yaml");
        let config = BenchmarkConfig::from_file(&path).unwrap();
        let runs = config
            .generate_benchmark_runs(Some("formula-transformations"))
            .unwrap();

        assert!(!runs.is_empty());
        assert!(runs.iter().all(|run| run.preprocess_exact_read_after_write));
    }

    #[test]
    fn selected_matrix_uses_the_same_generation_path_as_all_matrices() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benchmark_config.yaml");
        let config = BenchmarkConfig::from_file(&path).unwrap();
        let selected = config
            .generate_benchmark_runs(Some("formula-transformations"))
            .unwrap();
        let all = config.generate_benchmark_runs(None).unwrap();
        let selected_names = selected
            .iter()
            .map(|run| run.name.as_str())
            .collect::<std::collections::HashSet<_>>();
        let matching_all = all
            .iter()
            .filter(|run| selected_names.contains(run.name.as_str()))
            .count();

        assert_eq!(matching_all, selected.len());
    }
}
