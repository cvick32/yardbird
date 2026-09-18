//! Read-only inputs shared by refinement searches. Installation and history
//! updates remain with the coordinator.
use crate::{
    cost_functions::array::ArrayCostFactory,
    instantiation_strategy::assertion_tracker::canonical_instantiation_key,
    policy::effort::WorkAllowance,
    problem_context::ProblemContext,
    profiling::ArrayProfilingCollector,
    theories::array::instantiation_ranker::InstantiationRanker,
    theories::array::{
        array_axioms::{expr_to_term, ArrayExpr},
        array_rule_instantiator::ArrayArtifactCapture,
    },
};
use rustc_hash::FxHashMap;
use smt2parser::concrete::Term;
use std::{cell::RefCell, rc::Rc};

pub(super) struct SearchContext<'a, F: ArrayCostFactory> {
    pub smt: &'a dyn ProblemContext,
    pub term_config: &'a F::Config,
    pub ranker: &'a dyn InstantiationRanker,
    pub allowance: WorkAllowance,
    pub operation_id: Option<crate::policy::effort::OperationId>,
    pub pending_instances: &'a std::collections::HashSet<Term>,
    pub selection_counts: &'a FxHashMap<String, u32>,
    pub artifact_capture: ArrayArtifactCapture,
    pub depth: u16,
    pub refinement_step: u32,
    pub profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

impl<F: ArrayCostFactory> SearchContext<'_, F> {
    pub fn term_cost(
        &self,
        context: &crate::cost_functions::array::ArrayCostContext,
        depth: u32,
    ) -> F {
        F::from_context(context, depth, self.term_config)
    }
    pub fn installable_expression(&self, expression: &ArrayExpr) -> Option<Term> {
        let term = expr_to_term(expression.clone());
        self.smt
            .make_unquantified_instance(term)
            .map(|instance| canonical_instantiation_key(instance.get_term()))
    }
}
