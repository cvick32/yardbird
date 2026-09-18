//! Composed policy for the abstract array/binder strategy.
//!
//! Cost construction, complete-instance selection and effort settings have one owner.
//! The effort policy chooses work; the engine validates and executes it.

pub mod effort;
use crate::{
    cost_functions::array::{ArrayCostContext, ArrayCostFactory},
    theories::array::instantiation_ranker::{InstantiationRanker, PreferSourceInstantiationRanker},
};
pub use effort::{DefaultEffort, ProofEffort};

/// One policy configuration, retaining the existing term and ranker seams.
pub struct YardbirdPolicy<F: ArrayCostFactory> {
    term_config: F::Config,
    instances: Box<dyn InstantiationRanker>,
    effort: Box<dyn ProofEffort>,
}

impl<F: ArrayCostFactory> YardbirdPolicy<F> {
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

    pub fn term_cost(&self, context: &ArrayCostContext, depth: u32) -> F {
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
    use crate::{
        cost_functions::{
            array::{ArrayAstSize, LogisticRegression},
            YardbirdCostFunction,
        },
        training::LogisticRegressionModel,
    };

    #[test]
    fn learned_policy_preserves_contextual_selection() {
        let model = LogisticRegressionModel::from_path(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/policy_parity/learned-model.json"),
        )
        .unwrap();
        let policy = YardbirdPolicy::<LogisticRegression>::new(model);
        assert!(policy
            .term_cost(&ArrayCostContext::default(), 0)
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
