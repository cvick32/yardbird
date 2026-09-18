//! Composed policy for the abstract array/binder strategy.
//!
//! Cost construction, complete-instance selection and effort settings have one owner.
//! The effort policy chooses work; the engine validates and executes it.

pub mod effort;
pub mod instance_selection;
pub mod term_selection;
use crate::policy::instance_selection::{InstantiationRanker, PreferSourceInstantiationRanker};
use crate::policy::term_selection::context::TermCostContext;
use crate::policy::term_selection::TermCostFactory;
pub use effort::{DefaultEffort, ProofEffort};

/// Executable policies selected by name. Each constructs its own proof plan.
#[derive(clap::ValueEnum, Debug, Clone, Copy, PartialEq, Eq)]
pub enum NamedPolicy {
    /// German's BMC-cost policy with batched winners and property assumptions.
    GermanFast,
}

impl NamedPolicy {
    pub fn build_plan(self, run: &crate::YardbirdOptions) -> crate::ArrayProofPlan {
        match self {
            Self::GermanFast => german_fast(run),
        }
    }
}

fn german_fast(run: &crate::YardbirdOptions) -> crate::ArrayProofPlan {
    use crate::auxiliary_synthesis::ConditionalHistory;
    use crate::instance_installation::full_unroll::FullUnrollStrategy;
    use crate::policy::term_selection::array::ArrayBMCCost;
    use crate::solver::PropertyCheckMode;
    use crate::strategies::{Abstract, ProofStrategyExt, RefinementState};
    use crate::theories::array::array_egraph_builder::SourceThenFullEGraphBuilder;
    use crate::{ArrayProofPlan, SolverBackend};

    let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
        .with_instantiation_ranker(Box::new(PreferSourceInstantiationRanker))
        .with_effort(
            DefaultEffort::default()
                .with_egraph_builder(Box::<SourceThenFullEGraphBuilder>::default())
                .with_winners_per_group(20),
        );
    let strategy = Abstract::new(run.depth, run.run_ic3ia, policy, run.profiling_enabled())
        .with_artifact_capture(run.build_array_artifact_capture())
        .with_property_check_mode(PropertyCheckMode::Assumptions);
    let synthesis = run.build_aux_synthesis_config();
    let conditional_history = (!synthesis.is_off()).then(|| {
        Box::new(ConditionalHistory::<ArrayBMCCost>::new(synthesis, ()))
            as Box<dyn ProofStrategyExt<RefinementState>>
    });
    ArrayProofPlan {
        solver: SolverBackend::Z3,
        instantiation_strategy: Box::new(FullUnrollStrategy::new()),
        strategy: Box::new(strategy),
        conditional_history,
    }
}

/// One policy configuration, retaining the existing term and ranker seams.
pub struct YardbirdPolicy<F: TermCostFactory> {
    term_config: F::Config,
    instances: Box<dyn InstantiationRanker>,
    effort: Box<dyn ProofEffort>,
}

impl<F: TermCostFactory> YardbirdPolicy<F> {
    pub fn new(term_config: F::Config) -> Self {
        Self {
            term_config,
            instances: Box::new(PreferSourceInstantiationRanker),
            effort: Box::<DefaultEffort>::default(),
        }
    }

    pub fn with_term_config(mut self, config: F::Config) -> Self {
        self.term_config = config;
        self
    }

    pub fn with_instantiation_ranker(mut self, ranker: Box<dyn InstantiationRanker>) -> Self {
        self.instances = ranker;
        self
    }

    pub fn with_effort(mut self, effort: impl ProofEffort + 'static) -> Self {
        self.effort = Box::new(effort);
        self
    }

    pub fn term_cost(&self, context: &TermCostContext, depth: u32) -> F {
        F::from_context(context, depth, &self.term_config)
    }

    pub fn instantiation_ranker(&self) -> &dyn InstantiationRanker {
        self.instances.as_ref()
    }

    pub fn effort(&self) -> &dyn ProofEffort {
        self.effort.as_ref()
    }
    pub fn effort_mut(&mut self) -> &mut dyn ProofEffort {
        self.effort.as_mut()
    }
    pub(crate) fn parts(&mut self) -> (&F::Config, &dyn InstantiationRanker, &mut dyn ProofEffort) {
        (
            &self.term_config,
            self.instances.as_ref(),
            self.effort.as_mut(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::policy::term_selection::array::{ArrayAstSize, LogisticRegression};
    use crate::policy::term_selection::YardbirdCostFunction;
    use crate::training::LogisticRegressionModel;

    #[test]
    fn learned_policy_preserves_contextual_selection() {
        let model = LogisticRegressionModel::from_path(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/policy_parity/learned-model.json"),
        )
        .unwrap();
        let policy = YardbirdPolicy::<LogisticRegression>::new(model);
        assert!(policy
            .term_cost(&TermCostContext::default(), 0)
            .contextual_selector()
            .is_some());
    }

    #[test]
    #[should_panic(expected = "candidate groups need a winner")]
    fn zero_winner_allowance_is_invalid() {
        let _ = YardbirdPolicy::<ArrayAstSize>::new(())
            .with_effort(DefaultEffort::default().with_winners_per_group(0));
    }
}
