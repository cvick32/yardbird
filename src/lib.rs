#![warn(clippy::print_stdout)]

use std::{
    fmt::Display,
    fs::File,
    io::Write,
    path::{Path, PathBuf},
};

use crate::auxiliary_synthesis::{
    AuxRefinementRetention, AuxSynthesisConfig, ConditionalHistory, GuardPolicy,
    PredicateRelevancePolicy, SynthesisTrigger,
};
use clap::{Parser, Subcommand, ValueEnum};
pub use driver::{DepthCompletion, Driver, Error, ProofLoopResult, Result, RunProgress};
use serde::{Deserialize, Serialize};
use smt2parser::vmt::VMTModel;
use strategies::{
    Abstract, AbstractArrayWithQuantifiers, ConcreteArrayZ3, ListAbstract, ProofStrategy,
    ProofStrategyExt, RefinementState,
};

use crate::policy::instance_selection::{
    InstantiationRanker, PreferSourceInstantiationRanker, TermCostInstantiationRanker,
};
use crate::policy::term_selection::array::{
    AdaptiveArrayCost, ArrayAstSize, ArrayBMCCost, ArrayGenerated, ArrayPreferConstants,
    ArrayPreferRead, ArrayPreferWrite, IndexAwareArrayCost, LogisticRegression, ProtocolBmcCost,
    SplitArrayCost,
};
use crate::policy::term_selection::list::list_ast_size_cost_factory;
use crate::policy::term_selection::TermCostFactory;
use crate::rule_matching::candidate_builder::ArtifactCapture;
use crate::strategies::ListRefinementState;
use crate::theories::array::array_egraph_builder::{
    ArrayEGraphBuilder, ConeThenFullEGraphBuilder, FullEGraphBuilder, SourceThenFullEGraphBuilder,
};
use crate::training::LogisticRegressionModel;

pub mod audit;
pub mod auxiliary_synthesis;
pub mod countermodel;
mod driver;
mod egg_utils;
pub mod ic3ia;
pub mod instance_installation;
pub mod interpolant;
pub mod logger;
pub mod policy;
pub mod refinement_graph;
mod refinement_obligations;
pub use policy::YardbirdPolicy;
pub mod problem_context;
pub mod profiling;
mod proof_tree;
pub mod rule_matching;
pub mod smtlib_problem;
pub mod smtlib_refinement_session;
pub mod solver;
pub mod strategies;
mod subterm_handler;
pub mod terms;
pub mod theories;
pub use theories::preparation::TheorySelection;
pub mod theory_support;
pub mod training;
pub mod transition_index;
mod utils;
pub mod vmt_bmc_session;

/// The array strategy and optional extensions constructed from one CLI
/// configuration. Keeping them together ensures synthesis uses the same cost
/// configuration as ordinary array refinement.
pub struct ArrayProofPlan {
    pub solver: SolverBackend,
    pub instantiation_strategy: Box<dyn instance_installation::InstantiationStrategy>,
    pub strategy: Box<dyn ProofStrategy<'static, RefinementState>>,
    pub conditional_history: Option<Box<dyn ProofStrategyExt<RefinementState>>>,
}

#[derive(Parser, Debug, Clone, Serialize, Deserialize)]
#[command(version, about, long_about = None)]
pub struct YardbirdOptions {
    /// Run a repository-level operation instead of solving one input file.
    #[command(subcommand)]
    pub command: Option<YardbirdCommand>,

    /// Load every other option from this JSON file (a serialized
    /// `YardbirdOptions`), overriding whatever else was passed on the command
    /// line. Internal: `garden` uses this instead of reconstructing each flag
    /// as a subprocess argument.
    #[arg(long, hide = true)]
    #[serde(skip)]
    pub options_json: Option<PathBuf>,

    /// Select an executable policy instead of configuring individual policy choices.
    #[arg(long, value_enum, conflicts_with_all = [
        "strategy", "cost_function", "egraph_builder", "candidate_winners_per_group",
        "instantiation_ranker", "property_check_mode", "instantiation_strategy",
        "solver", "ranker_model", "preprocess_exact_read_after_write",
        "abstract_recurrent_products", "guarded_read_updates",
    ])]
    pub policy: Option<policy::NamedPolicy>,

    /// Name of the VMT file.
    #[arg(short, long)]
    pub filename: Option<String>,

    /// BMC depth until quitting.
    #[arg(short, long, default_value_t = 10)]
    pub depth: u16,

    /// Cooperative refinement wall timeout, checked between high-level actions (may overrun).
    #[arg(long)]
    pub wall_timeout_secs: Option<u64>,

    /// Atomically save VMT depth progress here, including before final JSON is available.
    #[arg(long)]
    pub progress_file: Option<std::path::PathBuf>,

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

    /// Choose how model equalities are admitted to the array refinement e-graph.
    #[arg(long, value_enum, default_value_t = EGraphBuilderStrategy::SourceThenFull)]
    pub egraph_builder: EGraphBuilderStrategy,

    /// Simplify exact select(store(A, i, v), i) terms before array abstraction.
    #[arg(long, default_value_t = false)]
    pub preprocess_exact_read_after_write: bool,

    /// Replace eligible nonlinear products with recurrent lookup tables.
    #[arg(long, default_value_t = false)]
    pub abstract_recurrent_products: bool,

    /// Add model-violated guarded read consequences of transition writes.
    #[arg(long, default_value_t = false)]
    pub guarded_read_updates: bool,

    /// Seed array axioms and VMT input binders once before checking, then replay.
    #[arg(long, default_value_t = false)]
    pub eager: bool,

    /// Number of ranked quantified-rule candidates selected from each refinement group.
    #[arg(long, default_value_t = 1)]
    pub candidate_winners_per_group: usize,

    /// Rank complete instantiations independently of the term cost function.
    #[arg(long, value_enum, default_value_t = InstantiationRankerStrategy::PreferSource)]
    pub instantiation_ranker: InstantiationRankerStrategy,

    /// How array VMT property checks are presented to the incremental solver.
    #[arg(long, value_enum, default_value_t = crate::solver::PropertyCheckMode::default())]
    pub property_check_mode: crate::solver::PropertyCheckMode,

    /// JSON logistic-regression model produced by tools/ml_ranker/train_ranker.py
    #[arg(long)]
    pub ranker_model: Option<String>,

    /// VMT theories for Yardbird to abstract: auto, none, or a comma-separated list (array,quantifiers).
    #[arg(short, long, default_value_t = TheorySelection::Auto)]
    pub theory: TheorySelection,

    // Choose Instantiation Strategy
    #[arg(long, value_enum, default_value_t = InstantiationStrategyType::FullUnroll)]
    pub instantiation_strategy: InstantiationStrategyType,

    /// Solver backend to use.
    #[arg(long, value_enum, default_value_t = SolverBackend::Z3)]
    pub solver: SolverBackend,

    /// Output ProofLoopResult as JSON to stdout (for garden integration)
    #[arg(long, default_value_t = false)]
    pub json_output: bool,

    /// Dump a replayable SMT2 file with check-sat and unsat-core commands when unsat is reached
    #[arg(long)]
    pub dump_solver: Option<String>,

    /// Track instantiations using Z3's assert-and-track for unsat core analysis
    #[arg(long, default_value_t = false)]
    pub track_instantiations: bool,

    /// Dump unsat core to JSON file when tracking is enabled and unsat is reached
    #[arg(long)]
    pub dump_unsat_core: Option<String>,

    /// Enable very verbose rule-search and instantiation tracing.
    #[arg(long, default_value_t = false)]
    pub verbose: bool,

    /// Capture Yardbird solver, driver, and e-graph profiling data.
    #[arg(long, default_value_t = false)]
    pub profile: bool,

    /// Bound read-only counter-model tracing per refinement (0 disables). Includes JSON profiling.
    #[arg(long, default_value_t = 0)]
    pub countermodel_trace_work: usize,

    /// Return after guided candidates, or supplement them with bounded
    /// dependency search. Only meaningful with `--policy countermodel-guided`;
    /// see `NamedPolicy::build_plan`.
    #[arg(long, value_enum, default_value_t = policy::effort::GuidanceSchedule::Immediate, requires = "policy")]
    pub guidance_schedule: policy::effort::GuidanceSchedule,

    /// Work per guided refinement trace (default: 1024). Requires
    /// --policy countermodel-guided; independent of diagnostic tracing.
    #[arg(long, requires = "policy")]
    #[serde(default)]
    pub guidance_work: Option<usize>,

    /// Order of quantified transition explanations (default: predecessor-first).
    /// Requires --policy countermodel-guided.
    #[arg(long, value_enum, requires = "policy")]
    #[serde(default)]
    pub guidance_transition_order: Option<policy::effort::GuidanceTransitionOrder>,

    /// When to trace action requirements (default: when-unproductive).
    /// Requires --policy countermodel-guided.
    #[arg(long, value_enum, requires = "policy")]
    #[serde(default)]
    pub guidance_action_requirements: Option<policy::effort::ActionRequirementGuidance>,

    /// Try array and background axioms before the standard refinement search.
    /// Bounded per model; VMT abstract strategy only. Off is the baseline.
    #[arg(long, default_value_t = false)]
    #[serde(default)]
    pub prefer_axioms: bool,

    /// Write a replayable solver session and its metadata to this directory.
    #[arg(long)]
    pub solver_capture_dir: Option<PathBuf>,

    /// Record full cost-function candidate decisions in the result.
    #[arg(long, default_value_t = false)]
    pub record_decisions: bool,

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

    /// Whether to retain the ordinary refinement replaced by a synthesized auxiliary.
    #[arg(long, value_enum, default_value_t = AuxRefinementRetention::KeepAll)]
    pub synthesis_refinement_retention: AuxRefinementRetention,

    /// How interpolant predicates qualify as relevant auxiliary capture guards.
    #[arg(long, value_enum, default_value_t = PredicateRelevancePolicy::ExactProperty)]
    pub synthesis_predicate_relevance: PredicateRelevancePolicy,

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
            command: None,
            options_json: None,
            policy: None,
            filename: None,
            depth: 10,
            wall_timeout_secs: None,
            progress_file: None,
            print_file: false,
            interpolate: false,
            strategy: Strategy::Abstract,
            repl: false,
            run_ic3ia: false,
            cost_function: CostFunction::BmcCost,
            egraph_builder: EGraphBuilderStrategy::SourceThenFull,
            preprocess_exact_read_after_write: false,
            abstract_recurrent_products: false,
            guarded_read_updates: false,
            eager: false,
            candidate_winners_per_group: 1,
            instantiation_ranker: InstantiationRankerStrategy::PreferSource,
            property_check_mode: crate::solver::PropertyCheckMode::default(),
            ranker_model: None,
            theory: TheorySelection::Auto,
            instantiation_strategy: InstantiationStrategyType::FullUnroll,
            solver: SolverBackend::Z3,
            json_output: false,
            dump_solver: None,
            track_instantiations: false,
            dump_unsat_core: None,
            verbose: false,
            profile: false,
            countermodel_trace_work: 0,
            guidance_schedule: policy::effort::GuidanceSchedule::Immediate,
            guidance_work: None,
            guidance_transition_order: None,
            guidance_action_requirements: None,
            prefer_axioms: false,
            solver_capture_dir: None,
            record_decisions: false,
            train: false,
            train_reset: false,
            database_url: None,
            training_run_version: None,
            synthesis_trigger: SynthesisTrigger::Off,
            synthesis_guard_policy: GuardPolicy::True,
            synthesis_refinement_retention: AuxRefinementRetention::KeepAll,
            synthesis_predicate_relevance: PredicateRelevancePolicy::ExactProperty,
            synthesis_after: None,
            synthesis_refinement_limit_window: None,
            synthesis_repeated_pattern_threshold: None,
        }
    }
}

#[derive(Subcommand, Debug, Clone, Serialize, Deserialize)]
pub enum YardbirdCommand {
    /// Run every VMT benchmark with concrete and abstract strategies in isolated subprocesses.
    Audit {
        /// File or directory containing VMT benchmarks.
        input: PathBuf,

        /// BMC depth used for every Yardbird run.
        #[arg(long, default_value_t = 1)]
        depth: u16,

        /// Hard timeout for each strategy/benchmark pair.
        #[arg(long, default_value_t = 1)]
        timeout_seconds: u64,

        /// Number of Yardbird subprocesses to run concurrently.
        #[arg(long, default_value_t = 4)]
        jobs: usize,
    },

    /// Internal parser probe used by the audit subprocess runner.
    #[command(name = "__audit-parse", hide = true)]
    InternalAuditParse {
        /// Single VMT file to parse.
        input: PathBuf,
    },
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
    ) -> Box<dyn instance_installation::InstantiationStrategy> {
        match self.instantiation_strategy {
            InstantiationStrategyType::FullUnroll => {
                Box::new(instance_installation::full_unroll::FullUnrollStrategy::new())
            }
            InstantiationStrategyType::NoUnrollOnLoop => {
                Box::new(instance_installation::no_unroll_on_loop::NoUnrollOnLoop::new())
            }
            InstantiationStrategyType::SchemaBatch => {
                Box::new(instance_installation::schema_batch::SchemaBatchStrategy::new())
            }
        }
    }

    pub fn build_aux_synthesis_config(&self) -> AuxSynthesisConfig {
        AuxSynthesisConfig {
            trigger: self.synthesis_trigger,
            guard_policy: self.synthesis_guard_policy,
            refinement_retention: self.synthesis_refinement_retention,
            predicate_relevance: self.synthesis_predicate_relevance,
            manual_after: self.synthesis_after,
            refinement_limit_window: self.synthesis_refinement_limit_window,
            repeated_pattern_threshold: self.synthesis_repeated_pattern_threshold,
        }
    }

    pub fn build_profiler(&self) -> Option<crate::profiling::Profiler> {
        self.profiling_enabled()
            .then(|| crate::profiling::Profiler::from_options(self))
    }

    pub fn build_solver_capture(&self) -> Option<crate::solver::SolverCapture> {
        self.solver_capture_dir
            .clone()
            .map(crate::solver::SolverCapture::new)
    }

    pub(crate) fn profiling_enabled(&self) -> bool {
        self.profile
            || self.train
            || self.solver_capture_dir.is_some()
            || self.countermodel_trace_work > 0
    }

    pub fn build_array_artifact_capture(&self) -> ArtifactCapture {
        let decisions = self.record_decisions || self.train;
        ArtifactCapture {
            decisions,
            instantiation_provenance: decisions || self.track_instantiations,
            conflicts: self.synthesis_trigger != SynthesisTrigger::Off,
        }
    }

    /// Resolve `--options-json` if it was given: load every other option from
    /// that file, replacing whatever else was parsed from the command line.
    /// `garden` writes a full `YardbirdOptions` there instead of reconstructing
    /// each flag as a subprocess argument.
    pub fn resolve(self) -> anyhow::Result<Self> {
        use anyhow::Context;
        let Some(path) = &self.options_json else {
            return Ok(self);
        };
        let json = std::fs::read_to_string(path)
            .with_context(|| format!("reading --options-json {}", path.display()))?;
        serde_json::from_str(&json)
            .with_context(|| format!("parsing --options-json {}", path.display()))
    }

    pub fn validate_smtlib_mode(&self) -> anyhow::Result<()> {
        anyhow::ensure!(
            matches!(&self.theory, TheorySelection::Auto)
                || self.theory == TheorySelection::Explicit(vec![Theory::Array]),
            "theory ownership selection is currently supported only for VMT inputs"
        );
        anyhow::ensure!(
            self.wall_timeout_secs.is_none(),
            "--wall-timeout-secs is currently supported only for VMT inputs"
        );
        if self.synthesis_trigger != SynthesisTrigger::Off {
            anyhow::bail!(
                "SMT-LIB mode does not support --synthesis-trigger {} yet; use --synthesis-trigger off until strategy-based SMT-LIB sessions support auxiliary specs",
                self.synthesis_trigger
            );
        }
        Ok(())
    }

    /// Reject search scheduling preferences where no supported search runs.
    pub fn validate_prefer_axioms_options(&self) -> anyhow::Result<()> {
        if self.prefer_axioms {
            anyhow::ensure!(
                (self.policy.is_some() || matches!(self.strategy, Strategy::Abstract))
                    && self
                        .filename
                        .as_deref()
                        .is_some_and(|f| f.ends_with(".vmt"))
                    && self.theory.legacy_theory() != Some(Theory::List),
                "--prefer-axioms requires a VMT input and the abstract array/quantifier strategy"
            );
        }
        Ok(())
    }

    /// Reject unsupported counter-model tracing modes instead of silently ignoring the option.
    pub fn validate_countermodel_trace_options(&self) -> anyhow::Result<()> {
        if self.guidance_transition_order.is_some() || self.guidance_action_requirements.is_some() {
            anyhow::ensure!(
                self.policy == Some(policy::NamedPolicy::CountermodelGuided),
                "guidance transition order and action requirements require --policy countermodel-guided"
            );
        }
        if let Some(work) = self.guidance_work {
            anyhow::ensure!(
                self.policy == Some(policy::NamedPolicy::CountermodelGuided) && work > 0,
                "--guidance-work requires --policy countermodel-guided and a positive work limit"
            );
        }
        if self.countermodel_trace_work > 0
            || self.policy == Some(policy::NamedPolicy::CountermodelGuided)
        {
            anyhow::ensure!(
                matches!(self.strategy, Strategy::Abstract) || self.policy.is_some(),
                "counter-model tracing currently requires the abstract strategy"
            );
            anyhow::ensure!(
                self.filename
                    .as_deref()
                    .is_some_and(|f| f.ends_with(".vmt")),
                "counter-model tracing currently requires a VMT input"
            );
            anyhow::ensure!(
                self.theory.includes(Theory::Array) || self.theory.includes(Theory::Quantifiers),
                "counter-model tracing requires array or quantifier ownership"
            );
            // cvc5's `eval_partial` only answers from values already captured
            // for other purposes; it never issues fresh queries. Guidance
            // would silently find almost nothing rather than fail loudly.
            anyhow::ensure!(
                matches!(self.solver, SolverBackend::Z3),
                "counter-model tracing currently requires the Z3 solver backend"
            );
        }
        Ok(())
    }

    /// Reject eager configurations that cannot install instances before a model.
    pub fn validate_eager_options(&self) -> anyhow::Result<()> {
        if self.eager {
            anyhow::ensure!(
                self.theory.includes(Theory::Array),
                "--eager currently supports --theory array only"
            );
            anyhow::ensure!(!matches!(self.instantiation_strategy, InstantiationStrategyType::SchemaBatch),
                "--eager requires a model-independent installer; use full-unroll or no-unroll-on-loop instead of schema-batch");
        }
        Ok(())
    }

    pub(crate) fn configure_eager_policy<F: TermCostFactory>(
        &self,
        policy: YardbirdPolicy<F>,
    ) -> YardbirdPolicy<F> {
        if self.eager {
            policy.with_eager_instantiation(policy::eager::EagerInstantiation::default())
        } else {
            policy
        }
    }

    /// Validate the guarded-update scope, checking the input format when known.
    /// Garden validates strategy settings before it discovers individual files.
    pub fn validate_guarded_read_updates(&self) -> anyhow::Result<()> {
        if self.guarded_read_updates
            && (!matches!(self.strategy, Strategy::Abstract)
                || !self.theory.includes(Theory::Array)
                || self.filename.as_deref().is_some_and(|filename| {
                    Path::new(filename)
                        .extension()
                        .and_then(|extension| extension.to_str())
                        != Some("vmt")
                }))
        {
            anyhow::bail!(
                "--guarded-read-updates requires VMT input, --theory array, and --strategy abstract"
            );
        }
        Ok(())
    }

    pub fn validate_theory_selection(&self) -> anyhow::Result<()> {
        if self.theory.legacy_theory().is_none() && !matches!(self.strategy, Strategy::Abstract) {
            let compatible = match self.strategy {
                Strategy::Concrete => {
                    matches!(&self.theory, TheorySelection::Auto)
                        || self.theory == TheorySelection::Explicit(vec![])
                }
                Strategy::AbstractWithQuantifiers => {
                    matches!(&self.theory, TheorySelection::Auto)
                        || self.theory == TheorySelection::Explicit(vec![Theory::Array])
                }
                Strategy::Abstract => true,
            };
            anyhow::ensure!(compatible,
                "--strategy {} conflicts with --theory {}; use --strategy abstract for explicit theory ownership",
                self.strategy, self.theory);
        }
        Ok(())
    }

    pub fn validate_solver_backend_available(&self) -> anyhow::Result<()> {
        match self.solver {
            SolverBackend::Z3 => Ok(()),
            SolverBackend::Cvc5 => {
                #[cfg(not(feature = "cvc5-backend"))]
                {
                    anyhow::bail!(
                        "--solver cvc5 requires building yardbird with `--features cvc5-backend`"
                    );
                }
                #[cfg(feature = "cvc5-backend")]
                {
                    Ok(())
                }
            }
        }
    }

    pub fn validate_solver_backend_for_vmt_mode(&self) -> anyhow::Result<()> {
        self.validate_solver_backend_available()?;
        match self.solver {
            SolverBackend::Z3 => Ok(()),
            SolverBackend::Cvc5 => {
                if self.theory.legacy_theory().is_some() {
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
        self.validate_solver_backend_available()?;
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
                if !matches!(self.strategy, Strategy::Abstract) && !self.eager {
                    anyhow::bail!(
                        "--cost-function logistic-regression requires --strategy abstract or --eager"
                    );
                }
                if !self.theory.includes(Theory::Array) {
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

    pub fn build_abstract_array_strategy<F>(&self, bmc_depth: u16) -> Abstract<F>
    where
        F: TermCostFactory<Config = ()> + 'static,
    {
        self.build_configured_abstract_array_strategy(bmc_depth, ())
    }

    pub fn build_logistic_regression_array_strategy(
        &self,
        bmc_depth: u16,
    ) -> Abstract<LogisticRegression> {
        let model_path = self
            .ranker_model
            .as_deref()
            .expect("--cost-function logistic-regression requires --ranker-model");
        let model = LogisticRegressionModel::from_path(model_path)
            .unwrap_or_else(|err| panic!("failed to configure logistic-regression model: {err}"));
        self.build_configured_abstract_array_strategy(bmc_depth, model)
    }

    fn build_configured_abstract_array_strategy<F>(
        &self,
        bmc_depth: u16,
        cost_config: F::Config,
    ) -> Abstract<F>
    where
        F: TermCostFactory + 'static,
    {
        let policy = YardbirdPolicy::new(cost_config)
            .with_effort(
                crate::policy::DefaultEffort::default()
                    .with_prefer_axioms(self.prefer_axioms)
                    .with_egraph_builder(self.build_array_egraph_builder())
                    .with_winners_per_group(self.candidate_winners_per_group),
            )
            .with_instantiation_ranker(self.build_instantiation_ranker());
        let policy = self.configure_eager_policy(policy);
        Abstract::new(bmc_depth, self.run_ic3ia, policy, self.profiling_enabled())
            .with_countermodel_trace_work(self.countermodel_trace_work)
            .with_artifact_capture(self.build_array_artifact_capture())
            .with_exact_read_after_write_preprocessing(self.preprocess_exact_read_after_write)
            .with_recurrent_product_abstraction(self.abstract_recurrent_products)
            .with_guarded_read_updates(self.guarded_read_updates)
            .with_theory_selection(self.theory.clone())
            .with_property_check_mode(self.property_check_mode)
    }

    fn build_costed_array_plan<F>(&self, cost_config: F::Config) -> ArrayProofPlan
    where
        F: TermCostFactory + 'static,
    {
        if !matches!(self.strategy, Strategy::Abstract) {
            let policy = self.configure_eager_policy(YardbirdPolicy::<F>::new(cost_config));
            let strategy: Box<dyn ProofStrategy<'static, RefinementState>> = match self.strategy {
                Strategy::Concrete => Box::new(
                    ConcreteArrayZ3::new(self.run_ic3ia)
                        .with_eager_policy(&policy)
                        .with_property_check_mode(self.property_check_mode),
                ),
                Strategy::AbstractWithQuantifiers => Box::new(
                    AbstractArrayWithQuantifiers::new(self.run_ic3ia)
                        .with_eager_policy(&policy)
                        .with_exact_read_after_write_preprocessing(
                            self.preprocess_exact_read_after_write,
                        )
                        .with_property_check_mode(self.property_check_mode),
                ),
                Strategy::Abstract => unreachable!(),
            };
            return ArrayProofPlan {
                solver: self.solver,
                instantiation_strategy: self.build_instantiation_strategy(),
                strategy,
                conditional_history: None,
            };
        }
        let strategy = Box::new(
            self.build_configured_abstract_array_strategy::<F>(self.depth, cost_config.clone()),
        );
        let config = self.build_aux_synthesis_config();
        let conditional_history = (!config.is_off()).then(|| {
            Box::new(ConditionalHistory::<F>::new(config, cost_config))
                as Box<dyn ProofStrategyExt<RefinementState>>
        });
        ArrayProofPlan {
            solver: self.solver,
            instantiation_strategy: self.build_instantiation_strategy(),
            strategy,
            conditional_history,
        }
    }

    pub fn build_instantiation_ranker(&self) -> Box<dyn InstantiationRanker> {
        match self.instantiation_ranker {
            InstantiationRankerStrategy::TermCost => Box::new(TermCostInstantiationRanker),
            InstantiationRankerStrategy::PreferSource => Box::new(PreferSourceInstantiationRanker),
        }
    }

    fn build_array_egraph_builder(&self) -> Box<dyn ArrayEGraphBuilder> {
        match self.egraph_builder {
            EGraphBuilderStrategy::Full => Box::<FullEGraphBuilder>::default(),
            EGraphBuilderStrategy::SourceThenFull => Box::<SourceThenFullEGraphBuilder>::default(),
            EGraphBuilderStrategy::ConeThenFull => Box::<ConeThenFullEGraphBuilder>::default(),
        }
    }

    pub fn build_array_proof_plan(&self) -> ArrayProofPlan {
        if let Some(policy) = self.policy {
            return policy.build_plan(self);
        }
        self.build_configured_array_proof_plan()
    }

    fn build_configured_array_proof_plan(&self) -> ArrayProofPlan {
        match self.cost_function {
            CostFunction::LogisticRegression => self.build_costed_array_plan::<LogisticRegression>(
                LogisticRegressionModel::from_path(
                    self.ranker_model
                        .as_deref()
                        .expect("--cost-function logistic-regression requires --ranker-model"),
                )
                .unwrap_or_else(|err| {
                    panic!("failed to configure logistic-regression model: {err}")
                }),
            ),
            CostFunction::BmcCost => self.build_costed_array_plan::<ArrayBMCCost>(()),
            CostFunction::ProtocolBmc => self.build_costed_array_plan::<ProtocolBmcCost>(()),
            CostFunction::AstSize => self.build_costed_array_plan::<ArrayAstSize>(()),
            CostFunction::AdaptiveCost => self.build_costed_array_plan::<AdaptiveArrayCost>(()),
            CostFunction::SplitCost => self.build_costed_array_plan::<SplitArrayCost>(()),
            CostFunction::PreferRead => self.build_costed_array_plan::<ArrayPreferRead>(()),
            CostFunction::PreferWrite => self.build_costed_array_plan::<ArrayPreferWrite>(()),
            CostFunction::PreferConstants => {
                self.build_costed_array_plan::<ArrayPreferConstants>(())
            }
            CostFunction::IndexAware => self.build_costed_array_plan::<IndexAwareArrayCost>(()),
            CostFunction::Generated => self.build_costed_array_plan::<ArrayGenerated>(()),
        }
    }

    pub fn build_array_strategy(&self) -> Box<dyn ProofStrategy<'static, RefinementState>> {
        self.build_array_proof_plan().strategy
    }

    pub fn build_list_strategy(&self) -> Box<dyn ProofStrategy<'_, ListRefinementState>> {
        match self.strategy {
            Strategy::Abstract => match self.cost_function {
                CostFunction::LogisticRegression => {
                    todo!("logistic-regression is not implemented for list theory")
                }
                CostFunction::BmcCost => todo!(),
                CostFunction::ProtocolBmc => {
                    todo!("protocol-bmc is not implemented for list theory")
                }
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
    ProtocolBmc,
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

#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize, Eq, PartialEq)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum EGraphBuilderStrategy {
    Full,
    SourceThenFull,
    ConeThenFull,
}

/// Policy for ranking complete grounded formulas after term extraction.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize, Eq, PartialEq)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum InstantiationRankerStrategy {
    TermCost,
    PreferSource,
}

impl Display for InstantiationRankerStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TermCost => write!(f, "term-cost"),
            Self::PreferSource => write!(f, "prefer-source"),
        }
    }
}

impl Display for EGraphBuilderStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Full => write!(f, "full"),
            Self::SourceThenFull => write!(f, "source-then-full"),
            Self::ConeThenFull => write!(f, "cone-then-full"),
        }
    }
}

impl Display for CostFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CostFunction::BmcCost => write!(f, "bmc-cost"),
            CostFunction::ProtocolBmc => write!(f, "protocol-bmc"),
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
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize, PartialEq, Eq)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum Theory {
    Array,
    Quantifiers,
    List,
}

impl Display for Theory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Theory::Array => write!(f, "array"),
            Theory::Quantifiers => write!(f, "quantifiers"),
            Theory::List => write!(f, "list"),
        }
    }
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
#[derive(Copy, Clone, Debug, PartialEq, Eq, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum InstantiationStrategyType {
    FullUnroll,
    NoUnrollOnLoop,
    SchemaBatch,
}

impl Display for InstantiationStrategyType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InstantiationStrategyType::FullUnroll => write!(f, "full-unroll"),
            InstantiationStrategyType::NoUnrollOnLoop => write!(f, "no-unroll-on-loop"),
            InstantiationStrategyType::SchemaBatch => write!(f, "schema-batch"),
        }
    }
}

#[cfg(test)]
mod option_tests {
    use super::*;

    #[test]
    fn prefer_axioms_is_opt_in_and_rejects_unsupported_search_modes() {
        let baseline = YardbirdOptions::from_filename("input.vmt".into());
        assert!(!baseline.prefer_axioms);
        let mut options =
            YardbirdOptions::try_parse_from(["yardbird", "-f", "input.vmt", "--prefer-axioms"])
                .unwrap();
        assert!(options.prefer_axioms);
        options.validate_prefer_axioms_options().unwrap();
        options.strategy = Strategy::Concrete;
        assert!(options.validate_prefer_axioms_options().is_err());
        options.policy = Some(policy::NamedPolicy::GermanFast);
        options.validate_prefer_axioms_options().unwrap();
        options.filename = Some("input.smt2".into());
        assert!(options.validate_prefer_axioms_options().is_err());
        let mut old = serde_json::to_value(baseline).unwrap();
        old.as_object_mut().unwrap().remove("prefer_axioms");
        assert!(
            !serde_json::from_value::<YardbirdOptions>(old)
                .unwrap()
                .prefer_axioms
        );
    }

    #[test]
    fn resolve_is_a_no_op_without_options_json() {
        let options =
            YardbirdOptions::try_parse_from(["yardbird", "-f", "input.vmt", "--depth", "17"])
                .unwrap();
        let before = format!("{options:?}");
        let resolved = options.resolve().unwrap();
        assert_eq!(format!("{resolved:?}"), before);
        assert!(resolved.options_json.is_none());
    }

    #[test]
    fn resolve_replaces_options_from_options_json() {
        // Cover distinct field kinds (a flag, a value_enum, a plain number,
        // Option<T>, a policy + the field it gates) so a field that can't
        // round-trip through serde would show up here. `--ranker-model`
        // conflicts with `--policy` at parse time, so it's set directly
        // rather than parsed alongside it.
        let mut written = YardbirdOptions::try_parse_from([
            "yardbird",
            "-f",
            "input.vmt",
            "--depth",
            "17",
            "--run-ic3ia",
            "--profile",
            "--policy",
            "countermodel-guided",
            "--guidance-schedule",
            "supplement",
        ])
        .unwrap();
        written.options_json = None;
        written.ranker_model = Some("model.json".to_string());
        let file = tempfile::NamedTempFile::new().unwrap();
        std::fs::write(file.path(), serde_json::to_string(&written).unwrap()).unwrap();

        let loaded = YardbirdOptions::try_parse_from([
            "yardbird",
            "--options-json",
            file.path().to_str().unwrap(),
        ])
        .unwrap()
        .resolve()
        .unwrap();

        assert_eq!(format!("{loaded:?}"), format!("{written:?}"));
    }

    #[test]
    fn resolve_reports_a_missing_options_json_file() {
        let options =
            YardbirdOptions::try_parse_from(["yardbird", "--options-json", "/no/such/file.json"])
                .unwrap();
        assert!(options.resolve().is_err());
    }

    #[test]
    fn guidance_schedule_requires_a_policy_instead_of_being_silently_ignored() {
        assert!(YardbirdOptions::try_parse_from([
            "yardbird",
            "-f",
            "input.vmt",
            "--guidance-schedule",
            "supplement",
        ])
        .is_err());

        let options = YardbirdOptions::try_parse_from([
            "yardbird",
            "-f",
            "input.vmt",
            "--policy",
            "countermodel-guided",
            "--guidance-schedule",
            "supplement",
        ])
        .unwrap();
        assert_eq!(
            options.guidance_schedule,
            policy::effort::GuidanceSchedule::Supplement
        );
    }

    #[test]
    fn guidance_work_requires_a_positive_limit_and_the_guided_policy() {
        assert!(YardbirdOptions::try_parse_from([
            "yardbird",
            "-f",
            "input.vmt",
            "--guidance-work",
            "4096"
        ])
        .is_err());
        for (policy, work, valid) in [
            ("countermodel-guided", "4096", true),
            ("countermodel-guided", "0", false),
            ("german-fast", "4096", false),
        ] {
            let options = YardbirdOptions::try_parse_from([
                "yardbird",
                "-f",
                "input.vmt",
                "--policy",
                policy,
                "--guidance-work",
                work,
            ])
            .unwrap();
            assert_eq!(options.validate_countermodel_trace_options().is_ok(), valid);
        }
        let mut old = serde_json::to_value(YardbirdOptions::default()).unwrap();
        old.as_object_mut().unwrap().remove("guidance_work");
        assert_eq!(
            serde_json::from_value::<YardbirdOptions>(old)
                .unwrap()
                .guidance_work,
            None
        );
    }

    #[test]
    fn guidance_order_and_requirements_cli_validate_policy_and_spelling() {
        for (flag, values) in [
            (
                "--guidance-transition-order",
                ["predecessor-only", "predecessor-first", "current-first"],
            ),
            (
                "--guidance-action-requirements",
                ["disabled", "when-unproductive", "always"],
            ),
        ] {
            for value in values {
                assert!(YardbirdOptions::try_parse_from([
                    "yardbird",
                    "-f",
                    "input.vmt",
                    flag,
                    value
                ])
                .is_err());
                for (policy, valid) in [("countermodel-guided", true), ("german-fast", false)] {
                    let options = YardbirdOptions::try_parse_from([
                        "yardbird",
                        "-f",
                        "input.vmt",
                        "--policy",
                        policy,
                        flag,
                        value,
                    ])
                    .unwrap();
                    assert_eq!(options.validate_countermodel_trace_options().is_ok(), valid);
                }
            }
            assert!(YardbirdOptions::try_parse_from([
                "yardbird",
                "-f",
                "input.vmt",
                "--policy",
                "countermodel-guided",
                flag,
                "misspelled"
            ])
            .is_err());
        }
        let mut old = serde_json::to_value(YardbirdOptions::default()).unwrap();
        for key in ["guidance_transition_order", "guidance_action_requirements"] {
            old.as_object_mut().unwrap().remove(key);
        }
        let decoded: YardbirdOptions = serde_json::from_value(old).unwrap();
        assert!(decoded.guidance_transition_order.is_none());
        assert!(decoded.guidance_action_requirements.is_none());
    }

    #[test]
    fn named_policies_build_abstract_plans_independently_of_individual_options() {
        let mut run = YardbirdOptions::from_filename("input.vmt".into());
        run.strategy = Strategy::Concrete;
        run.cost_function = CostFunction::LogisticRegression;
        run.property_check_mode = crate::solver::PropertyCheckMode::Scoped;
        run.solver = SolverBackend::Cvc5;
        run.instantiation_strategy = InstantiationStrategyType::NoUnrollOnLoop;
        let before = format!("{run:?}");
        for policy in [
            policy::NamedPolicy::GermanFast,
            policy::NamedPolicy::CountermodelGuided,
        ] {
            let plan = policy.build_plan(&run);
            assert_eq!(plan.solver, SolverBackend::Z3);
            assert_eq!(
                plan.strategy.property_check_mode(),
                crate::solver::PropertyCheckMode::Assumptions
            );
            assert_eq!(plan.strategy.refinement_limit(), None);
            assert_eq!(
                format!("{:?}", plan.instantiation_strategy),
                format!(
                    "{:?}",
                    instance_installation::full_unroll::FullUnrollStrategy::new()
                )
            );
        }
        assert_eq!(format!("{run:?}"), before);
    }

    #[test]
    fn property_checks_default_to_assumptions_and_allow_scoped_override() {
        use crate::solver::PropertyCheckMode;

        for strategy in ["abstract", "abstract-with-quantifiers", "concrete"] {
            for mode in [None, Some("scoped")] {
                let mut args = vec!["yardbird", "-f", "input.vmt", "-s", strategy];
                if let Some(mode) = mode {
                    args.extend(["--property-check-mode", mode]);
                }
                let options = YardbirdOptions::try_parse_from(args).unwrap();
                let expected = if mode.is_some() {
                    PropertyCheckMode::Scoped
                } else {
                    PropertyCheckMode::Assumptions
                };
                assert_eq!(options.property_check_mode, expected);
                assert_eq!(
                    options.build_array_strategy().property_check_mode(),
                    expected
                );
            }
        }
        assert_eq!(
            YardbirdOptions::from_filename("input.vmt".into())
                .build_array_strategy()
                .property_check_mode(),
            PropertyCheckMode::Assumptions
        );
    }

    #[test]
    fn exact_read_after_write_preprocessing_is_disabled_by_default() {
        let options = YardbirdOptions::from_filename("input.vmt".to_string());

        assert!(!options.preprocess_exact_read_after_write);
        assert!(!options
            .build_array_strategy()
            .preprocess_exact_read_after_write());
    }

    #[test]
    fn cli_flag_enables_exact_read_after_write_preprocessing() {
        let options = YardbirdOptions::try_parse_from([
            "yardbird",
            "--filename",
            "input.vmt",
            "--preprocess-exact-read-after-write",
        ])
        .unwrap();

        assert!(options.preprocess_exact_read_after_write);
        assert!(options
            .build_array_strategy()
            .preprocess_exact_read_after_write());
    }

    #[test]
    fn guarded_read_updates_are_explicit_and_disabled_by_default() {
        assert!(!YardbirdOptions::from_filename("input.vmt".into()).guarded_read_updates);
        let options = YardbirdOptions::try_parse_from([
            "yardbird",
            "--filename",
            "input.vmt",
            "--guarded-read-updates",
        ])
        .unwrap();
        assert!(options.guarded_read_updates);
        assert!(!options.abstract_recurrent_products);
    }

    #[test]
    fn recurrent_product_encoding_is_an_explicit_cli_dimension() {
        let defaults = YardbirdOptions::from_filename("input.vmt".to_string());
        assert!(!defaults.abstract_recurrent_products);

        let enabled = YardbirdOptions::try_parse_from([
            "yardbird",
            "--filename",
            "input.vmt",
            "--abstract-recurrent-products",
        ])
        .unwrap();
        assert!(enabled.abstract_recurrent_products);
    }

    #[test]
    fn egraph_builder_strategy_is_an_explicit_cli_dimension() {
        let default_options = YardbirdOptions::from_filename("input.vmt".to_string());
        assert_eq!(
            default_options.egraph_builder,
            EGraphBuilderStrategy::SourceThenFull
        );

        let staged_options = YardbirdOptions::try_parse_from([
            "yardbird",
            "--filename",
            "input.vmt",
            "--egraph-builder",
            "source-then-full",
            "--instantiation-ranker",
            "term-cost",
        ])
        .unwrap();

        assert_eq!(
            staged_options.egraph_builder,
            EGraphBuilderStrategy::SourceThenFull
        );
        assert_eq!(
            staged_options.instantiation_ranker,
            InstantiationRankerStrategy::TermCost
        );
    }
}
