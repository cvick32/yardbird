//! Composed policy for the abstract array/binder strategy.
//!
//! Cost construction, complete-instance selection and effort settings have one owner.
//! Phase dispatch, matching and model state still live in the existing engine.
//! In particular,
//! this checkpoint does not claim that all effort decisions are replaceable.

use std::{collections::HashSet, num::NonZeroUsize};

use crate::{
    cost_functions::array::{ArrayCostContext, ArrayCostFactory},
    theories::array::{
        array_egraph_builder::{ArrayEGraphBuilder, SourceThenFullEGraphBuilder},
        instantiation_ranker::{InstantiationRanker, PreferSourceInstantiationRanker},
    },
};

/// Default allowances and graph construction. Adaptive allocation and the
/// operation-based effort interface are later checkpoints.
pub struct DefaultEffort {
    winners_per_group: NonZeroUsize,
    egraph_builder: Box<dyn ArrayEGraphBuilder>,
}

impl Default for DefaultEffort {
    fn default() -> Self {
        Self {
            winners_per_group: NonZeroUsize::new(1).unwrap(),
            egraph_builder: Box::<SourceThenFullEGraphBuilder>::default(),
        }
    }
}

impl DefaultEffort {
    const DEPENDENCY_SKIP_PERIOD: u32 = 8;
    const DEPENDENCY_REQUEST_LIMIT: usize = 32;

    pub fn with_winners_per_group(mut self, winners: usize) -> Self {
        self.winners_per_group =
            NonZeroUsize::new(winners).expect("candidate groups need a winner");
        self
    }

    pub fn with_egraph_builder(mut self, builder: Box<dyn ArrayEGraphBuilder>) -> Self {
        self.egraph_builder = builder;
        self
    }

    pub fn winners_per_group(&self) -> usize {
        self.winners_per_group.get()
    }

    pub(crate) fn permits_dependency_pass(&self, refinement_step: u32) -> bool {
        refinement_step % Self::DEPENDENCY_SKIP_PERIOD != Self::DEPENDENCY_SKIP_PERIOD - 1
    }

    pub(crate) fn dependency_request_limit(&self) -> usize {
        Self::DEPENDENCY_REQUEST_LIMIT
    }

    pub(crate) fn builder_for_refinement(
        &self,
        attempted_depths: &mut HashSet<u16>,
        depth: u16,
    ) -> Box<dyn ArrayEGraphBuilder> {
        self.egraph_builder
            .clone_for_refinement(attempted_depths, depth)
    }

    pub(crate) fn requires_property_cone(&self) -> bool {
        self.egraph_builder.requires_property_cone()
    }
}

/// One policy configuration, retaining the existing term and ranker seams.
pub struct YardbirdPolicy<F: ArrayCostFactory> {
    term_config: F::Config,
    instances: Box<dyn InstantiationRanker>,
    effort: DefaultEffort,
}

impl<F: ArrayCostFactory> YardbirdPolicy<F> {
    pub fn new(term_config: F::Config) -> Self {
        Self {
            term_config,
            instances: Box::new(PreferSourceInstantiationRanker),
            effort: DefaultEffort::default(),
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

    pub fn with_effort(mut self, effort: DefaultEffort) -> Self {
        self.effort = effort;
        self
    }

    pub fn with_candidate_winners_per_group(mut self, winners: usize) -> Self {
        self.effort = self.effort.with_winners_per_group(winners);
        self
    }

    pub fn with_egraph_builder(mut self, builder: Box<dyn ArrayEGraphBuilder>) -> Self {
        self.effort = self.effort.with_egraph_builder(builder);
        self
    }

    pub fn term_cost(&self, context: &ArrayCostContext, depth: u32) -> F {
        F::from_context(context, depth, &self.term_config)
    }

    pub fn instantiation_ranker(&self) -> &dyn InstantiationRanker {
        self.instances.as_ref()
    }

    pub fn effort(&self) -> &DefaultEffort {
        &self.effort
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
        let _ = YardbirdPolicy::<ArrayAstSize>::new(()).with_candidate_winners_per_group(0);
    }
}
