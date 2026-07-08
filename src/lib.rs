#![warn(clippy::print_stdout)]

use std::{fmt::Display, fs::File, io::Write};

use crate::auxiliary_synthesis::{AuxSynthesisConfig, GuardPolicy, SynthesisTrigger};
use clap::{Parser, ValueEnum};
pub use driver::{Driver, Error, ProofLoopResult, Result};
use serde::{Deserialize, Serialize};
use smt2parser::vmt::VMTModel;
use strategies::{
    Abstract, AbstractArrayWithQuantifiers, ArrayRefinementState, ConcreteArrayZ3, ListAbstract,
    ProofStrategy,
};

use crate::{
    cost_functions::{
        array::{
            AdaptiveArrayCost, ArrayAstSize, ArrayBMCCost, ArrayCostFactory, ArrayGenerated,
            ArrayPreferConstants, ArrayPreferRead, ArrayPreferWrite, IndexAwareArrayCost,
            LogisticRegression, SplitArrayCost,
        },
        list::list_ast_size_cost_factory,
    },
    strategies::ListRefinementState,
    training::LogisticRegressionModel,
};

pub mod auxiliary_synthesis;
pub mod cost_functions;
mod driver;
mod egg_utils;
pub mod ic3ia;
pub mod instantiation_strategy;
mod interpolant;
pub mod logger;
pub mod problem_context;
pub mod profiling;
mod proof_tree;
pub mod smt_problem;
pub mod smtlib_problem;
pub mod smtlib_smt_problem;
pub mod solver;
pub mod strategies;
mod subterm_handler;
pub mod theories;
pub mod theory_support;
pub mod training;
mod utils;

#[derive(Parser, Debug, Clone)]
#[command(version, about, long_about = None)]
pub struct YardbirdOptions {
    /// Name of the VMT file.
    #[arg(short, long)]
    pub filename: Option<String>,

    /// BMC depth until quitting.
    #[arg(short, long, default_value_t = 10)]
    pub depth: u16,

    /// Output VMT files before and after instantiation.
    #[arg(short, long, default_value_t = false)]
    pub print_file: bool,

    /// Run SMTInterpol when BMC depth is UNSAT
    #[arg(short, long, default_value_t = false)]
    pub interpolate: bool,

    #[arg(short, long, value_enum, default_value_t = Strategy::Abstract)]
    pub strategy: Strategy,

    /// Interactive mode.
    #[arg(long, default_value_t = false)]
    pub repl: bool,

    // Invoke IC3IA
    #[arg(long, default_value_t = false)]
    pub run_ic3ia: bool,

    // Choose Cost Function
    #[arg(short, long, value_enum, default_value_t = CostFunction::BmcCost)]
    pub cost_function: CostFunction,

    /// JSON logistic-regression model produced by tools/ml_ranker/train_ranker.py
    #[arg(long)]
    pub ranker_model: Option<String>,

    // Choose Theory
    #[arg(short, long, value_enum, default_value_t = Theory::Array)]
    pub theory: Theory,

    // Choose Instantiation Strategy
    #[arg(long, value_enum, default_value_t = InstantiationStrategyType::FullUnroll)]
    pub instantiation_strategy: InstantiationStrategyType,

    /// Solver backend to use.
    #[arg(long, value_enum, default_value_t = SolverBackend::Z3)]
    pub solver: SolverBackend,

    /// Output ProofLoopResult as JSON to stdout (for garden integration)
    #[arg(long, default_value_t = false)]
    pub json_output: bool,

    /// Dump solver state to SMT2 file when unsat is reached
    #[arg(long)]
    pub dump_solver: Option<String>,

    /// Track instantiations using Z3's assert-and-track for unsat core analysis
    #[arg(long, default_value_t = false)]
    pub track_instantiations: bool,

    /// Dump unsat core to JSON file when tracking is enabled and unsat is reached
    #[arg(long)]
    pub dump_unsat_core: Option<String>,

    /// Enable very verbose conflict scheduler and instantiation tracing.
    #[arg(long, default_value_t = false)]
    pub verbose: bool,

    /// Capture Yardbird-side profiling data, especially e-graph cost computation timings.
    #[arg(long, default_value_t = false)]
    pub profile_costs: bool,

    /// Enable training data logging to database
    #[arg(long, default_value_t = false)]
    pub train: bool,

    /// Clear all training tables in the configured database and exit.
    #[arg(long, default_value_t = false)]
    pub train_reset: bool,

    /// Database URL for training data (e.g., postgres://user:pass@host/db)
    #[arg(long, env = "YARDBIRD_DATABASE_URL")]
    pub database_url: Option<String>,

    /// Stable identifier that groups many benchmark rows into one training campaign
    #[arg(long, env = "YARDBIRD_TRAINING_RUN_VERSION")]
    pub training_run_version: Option<String>,

    /// When to trigger auxiliary prophecy/history synthesis.
    #[arg(long, value_enum, default_value_t = SynthesisTrigger::Off)]
    pub synthesis_trigger: SynthesisTrigger,

    /// How to synthesize capture guards for auxiliary history variables.
    #[arg(long, value_enum, default_value_t = GuardPolicy::True)]
    pub synthesis_guard_policy: GuardPolicy,

    /// Refinement step threshold for --synthesis-trigger manual-after-n.
    #[arg(long)]
    pub synthesis_after: Option<u32>,

    /// Remaining-refinement window for --synthesis-trigger refinement-limit.
    #[arg(long)]
    pub synthesis_refinement_limit_window: Option<u32>,

    /// Repetition threshold for --synthesis-trigger repeated-pattern.
    #[arg(long)]
    pub synthesis_repeated_pattern_threshold: Option<u32>,
}

impl Default for YardbirdOptions {
    fn default() -> Self {
        YardbirdOptions {
            filename: None,
            depth: 10,
            print_file: false,
            interpolate: false,
            strategy: Strategy::Abstract,
            repl: false,
            run_ic3ia: false,
            cost_function: CostFunction::BmcCost,
            ranker_model: None,
            theory: Theory::Array,
            instantiation_strategy: InstantiationStrategyType::FullUnroll,
            solver: SolverBackend::Z3,
            json_output: false,
            dump_solver: None,
            track_instantiations: false,
            dump_unsat_core: None,
            verbose: false,
            profile_costs: false,
            train: false,
            train_reset: false,
            database_url: None,
            training_run_version: None,
            synthesis_trigger: SynthesisTrigger::Off,
            synthesis_guard_policy: GuardPolicy::True,
            synthesis_after: None,
            synthesis_refinement_limit_window: None,
            synthesis_repeated_pattern_threshold: None,
        }
    }
}

impl YardbirdOptions {
    pub fn from_filename(filename: String) -> Self {
        YardbirdOptions {
            filename: Some(filename),
            ..Default::default()
        }
    }

    pub fn require_filename(&self) -> anyhow::Result<&str> {
        self.filename
            .as_deref()
            .ok_or_else(|| anyhow::anyhow!("--filename is required unless --train-reset is used"))
    }

    pub fn build_instantiation_strategy(
        &self,
    ) -> Box<dyn instantiation_strategy::InstantiationStrategy> {
        match self.instantiation_strategy {
            InstantiationStrategyType::FullUnroll => {
                Box::new(instantiation_strategy::full_unroll::FullUnrollStrategy::new())
            }
            InstantiationStrategyType::NoUnrollOnLoop => {
                Box::new(instantiation_strategy::no_unroll_on_loop::NoUnrollOnLoop::new())
            }
        }
    }

    pub fn build_aux_synthesis_config(&self) -> AuxSynthesisConfig {
        AuxSynthesisConfig {
            trigger: self.synthesis_trigger,
            guard_policy: self.synthesis_guard_policy,
            manual_after: self.synthesis_after,
            refinement_limit_window: self.synthesis_refinement_limit_window,
            repeated_pattern_threshold: self.synthesis_repeated_pattern_threshold,
        }
    }

    pub fn validate_smtlib_mode(&self) -> anyhow::Result<()> {
        if self.synthesis_trigger != SynthesisTrigger::Off {
            anyhow::bail!(
                "SMT-LIB mode does not support --synthesis-trigger {} yet; use --synthesis-trigger off until SMTLIBSMTProblem can install auxiliary specs",
                self.synthesis_trigger
            );
        }
        Ok(())
    }

    pub fn validate_solver_backend_for_vmt_mode(&self) -> anyhow::Result<()> {
        match self.solver {
            SolverBackend::Z3 => Ok(()),
            SolverBackend::Cvc5 => {
                if !matches!(self.theory, Theory::Array) {
                    anyhow::bail!(
                        "--solver cvc5 in VMT mode currently supports array theory only; {:?} theory is not implemented yet",
                        self.theory
                    );
                }
                Ok(())
            }
        }
    }

    pub fn validate_solver_backend_for_strategy_mode(&self) -> anyhow::Result<()> {
        match self.solver {
            SolverBackend::Z3 => Ok(()),
            SolverBackend::Cvc5 => anyhow::bail!(
                "--solver cvc5 is available for SMT-LIB simple mode in this phase, but strategy/refinement mode is not implemented until a later phase"
            ),
        }
    }

    pub fn validate_ranker_options(&self) -> anyhow::Result<()> {
        match (self.cost_function, self.ranker_model.as_ref()) {
            (CostFunction::LogisticRegression, None) => {
                anyhow::bail!(
                    "--cost-function logistic-regression requires --ranker-model <MODEL_JSON>"
                )
            }
            (CostFunction::LogisticRegression, Some(model_path)) => {
                if !matches!(self.strategy, Strategy::Abstract) {
                    anyhow::bail!(
                        "--cost-function logistic-regression currently requires --strategy abstract"
                    );
                }
                if !matches!(self.theory, Theory::Array) {
                    anyhow::bail!(
                        "--cost-function logistic-regression currently supports --theory array only"
                    );
                }
                LogisticRegressionModel::from_path(model_path).map_err(|err| {
                    anyhow::anyhow!("failed to load --ranker-model from {model_path}: {err}")
                })?;
                Ok(())
            }
            (_, Some(_)) => anyhow::bail!(
                "--ranker-model is only valid with --cost-function logistic-regression; run baseline cost functions without --ranker-model"
            ),
            (_, None) => Ok(()),
        }
    }

    pub fn build_abstract_array_strategy<F>(
        &self,
        bmc_depth: u16,
        aux_config: AuxSynthesisConfig,
    ) -> Abstract<F>
    where
        F: ArrayCostFactory<Config = ()> + 'static,
    {
        Abstract::new(
            bmc_depth,
            self.run_ic3ia,
            (),
            aux_config,
            self.profile_costs,
        )
    }

    pub fn build_logistic_regression_array_strategy(
        &self,
        bmc_depth: u16,
        aux_config: AuxSynthesisConfig,
    ) -> Abstract<LogisticRegression> {
        let model_path = self
            .ranker_model
            .as_deref()
            .expect("--cost-function logistic-regression requires --ranker-model");
        let model = LogisticRegressionModel::from_path(model_path)
            .unwrap_or_else(|err| panic!("failed to configure logistic-regression model: {err}"));
        Abstract::new(
            bmc_depth,
            self.run_ic3ia,
            model,
            aux_config,
            self.profile_costs,
        )
    }

    pub fn build_array_strategy(&self) -> Box<dyn ProofStrategy<'static, ArrayRefinementState>> {
        let aux_config = self.build_aux_synthesis_config();
        match self.strategy {
            Strategy::Abstract => match self.cost_function {
                CostFunction::LogisticRegression => {
                    Box::new(self.build_logistic_regression_array_strategy(self.depth, aux_config))
                }
                CostFunction::BmcCost => Box::new(
                    self.build_abstract_array_strategy::<ArrayBMCCost>(self.depth, aux_config),
                ),
                CostFunction::AstSize => Box::new(
                    self.build_abstract_array_strategy::<ArrayAstSize>(self.depth, aux_config),
                ),
                CostFunction::AdaptiveCost => Box::new(
                    self.build_abstract_array_strategy::<AdaptiveArrayCost>(self.depth, aux_config),
                ),
                CostFunction::SplitCost => Box::new(
                    self.build_abstract_array_strategy::<SplitArrayCost>(self.depth, aux_config),
                ),
                CostFunction::PreferRead => Box::new(
                    self.build_abstract_array_strategy::<ArrayPreferRead>(self.depth, aux_config),
                ),
                CostFunction::PreferWrite => Box::new(
                    self.build_abstract_array_strategy::<ArrayPreferWrite>(self.depth, aux_config),
                ),
                CostFunction::PreferConstants => {
                    Box::new(self.build_abstract_array_strategy::<ArrayPreferConstants>(
                        self.depth, aux_config,
                    ))
                }
                CostFunction::IndexAware => {
                    Box::new(self.build_abstract_array_strategy::<IndexAwareArrayCost>(
                        self.depth, aux_config,
                    ))
                }
                CostFunction::Generated => Box::new(
                    self.build_abstract_array_strategy::<ArrayGenerated>(self.depth, aux_config),
                ),
            },
            Strategy::AbstractWithQuantifiers => {
                Box::new(AbstractArrayWithQuantifiers::new(self.run_ic3ia))
            }
            Strategy::Concrete => Box::new(ConcreteArrayZ3::new(self.run_ic3ia)),
        }
    }

    pub fn build_bvlist_strategy(&self) -> Box<dyn ProofStrategy<'static, ArrayRefinementState>> {
        let aux_config = self.build_aux_synthesis_config();
        // For now, use the same strategy structure as arrays
        // TODO: Create proper bit-vector list strategy
        match self.strategy {
            Strategy::Abstract => match self.cost_function {
                CostFunction::LogisticRegression => {
                    todo!("logistic-regression is not implemented for bv-list theory")
                }
                CostFunction::BmcCost => Box::new(
                    self.build_abstract_array_strategy::<ArrayBMCCost>(self.depth, aux_config),
                ),
                CostFunction::AstSize => Box::new(
                    self.build_abstract_array_strategy::<ArrayAstSize>(self.depth, aux_config),
                ),
                CostFunction::AdaptiveCost => Box::new(
                    self.build_abstract_array_strategy::<AdaptiveArrayCost>(self.depth, aux_config),
                ),
                CostFunction::SplitCost => Box::new(
                    self.build_abstract_array_strategy::<SplitArrayCost>(self.depth, aux_config),
                ),
                CostFunction::PreferRead => Box::new(
                    self.build_abstract_array_strategy::<ArrayPreferRead>(self.depth, aux_config),
                ),
                CostFunction::PreferWrite => Box::new(
                    self.build_abstract_array_strategy::<ArrayPreferWrite>(self.depth, aux_config),
                ),
                CostFunction::PreferConstants => todo!(),
                CostFunction::IndexAware => {
                    Box::new(self.build_abstract_array_strategy::<IndexAwareArrayCost>(
                        self.depth, aux_config,
                    ))
                }
                CostFunction::Generated => todo!(),
            },
            Strategy::AbstractWithQuantifiers => {
                Box::new(AbstractArrayWithQuantifiers::new(self.run_ic3ia))
            }
            Strategy::Concrete => Box::new(ConcreteArrayZ3::new(self.run_ic3ia)),
        }
    }

    pub fn build_list_strategy(&self) -> Box<dyn ProofStrategy<'_, ListRefinementState>> {
        match self.strategy {
            Strategy::Abstract => match self.cost_function {
                CostFunction::LogisticRegression => {
                    todo!("logistic-regression is not implemented for list theory")
                }
                CostFunction::BmcCost => todo!(),
                CostFunction::AstSize => Box::new(ListAbstract::new(
                    self.depth,
                    self.run_ic3ia,
                    list_ast_size_cost_factory,
                )),
                CostFunction::AdaptiveCost => todo!(),
                CostFunction::SplitCost => todo!(),
                CostFunction::PreferRead => todo!(),
                CostFunction::PreferWrite => todo!(),
                CostFunction::PreferConstants => todo!(),
                CostFunction::IndexAware => todo!(),
                CostFunction::Generated => todo!(),
            },
            Strategy::AbstractWithQuantifiers => {
                todo!("AbstractWithQuantifiers not yet implemented for List theory")
            }
            Strategy::Concrete => {
                todo!()
            }
        }
    }
}

pub fn model_from_options(options: &YardbirdOptions) -> VMTModel {
    let filename = options.require_filename().unwrap();
    let vmt_model = VMTModel::from_path(filename).unwrap();

    if options.print_file {
        let mut output = File::create("original.vmt").unwrap();
        let _ = output.write(vmt_model.as_vmt_string().as_bytes());
    }
    vmt_model
}

/// Describes the proving strategies available.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum Strategy {
    Abstract,
    AbstractWithQuantifiers,
    Concrete,
}

impl Display for Strategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Strategy::Abstract => write!(f, "abstract"),
            Strategy::AbstractWithQuantifiers => write!(f, "abstract-with-quantifiers"),
            Strategy::Concrete => write!(f, "concrete"),
        }
    }
}

/// Describes the cost functions available.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize, Eq, PartialEq)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum CostFunction {
    BmcCost,
    AstSize,
    AdaptiveCost,
    SplitCost,
    PreferRead,
    PreferWrite,
    PreferConstants,
    IndexAware,
    Generated,
    LogisticRegression,
}

impl Display for CostFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CostFunction::BmcCost => write!(f, "bmc-cost"),
            CostFunction::AstSize => write!(f, "ast-size"),
            CostFunction::AdaptiveCost => write!(f, "adaptive-cost"),
            CostFunction::SplitCost => write!(f, "split-cost"),
            CostFunction::PreferRead => write!(f, "prefer-read"),
            CostFunction::PreferWrite => write!(f, "prefer-write"),
            CostFunction::PreferConstants => write!(f, "prefer-constants"),
            CostFunction::IndexAware => write!(f, "index-aware"),
            CostFunction::Generated => write!(f, "generated"),
            CostFunction::LogisticRegression => write!(f, "logistic-regression"),
        }
    }
}

/// Describes the theories available.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum Theory {
    Array,
    BvList,
    List,
}

/// Describes the solver backends available.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize, Eq, PartialEq)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum SolverBackend {
    Z3,
    Cvc5,
}

impl Display for SolverBackend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SolverBackend::Z3 => write!(f, "z3"),
            SolverBackend::Cvc5 => write!(f, "cvc5"),
        }
    }
}

/// Describes the instantiation strategies available.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum InstantiationStrategyType {
    FullUnroll,
    NoUnrollOnLoop,
}

impl Display for InstantiationStrategyType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstantiationStrategyType::FullUnroll => write!(f, "full-unroll"),
            InstantiationStrategyType::NoUnrollOnLoop => write!(f, "no-unroll-on-loop"),
        }
    }
}
