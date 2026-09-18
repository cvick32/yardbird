//! Read-only inputs shared by refinement searches. Installation and history
//! updates remain with the coordinator.
use crate::instance_installation::assertion_tracker::canonical_instantiation_key;
use crate::policy::effort::WorkAllowance;
use crate::policy::instance_selection::InstantiationRanker;
use crate::policy::term_selection::TermCostFactory;
use crate::problem_context::ProblemContext;
use crate::profiling::RefinementProfilingCollector;
use crate::rule_matching::candidate_builder::ArtifactCapture;
use crate::terms::language::{expr_to_term, TermExpr};
use rustc_hash::FxHashMap;
use smt2parser::concrete::Term;
use std::{cell::RefCell, rc::Rc};

pub(crate) struct SearchContext<'a, F: TermCostFactory> {
    pub graph: &'a crate::refinement_graph::RefinementGraph,
    pub graph_version: u64,
    pub smt: &'a dyn ProblemContext,
    pub term_config: &'a F::Config,
    pub ranker: &'a dyn InstantiationRanker,
    pub allowance: WorkAllowance,
    pub operation_id: Option<crate::policy::effort::OperationId>,
    pub pending_instances: &'a std::collections::HashSet<Term>,
    pub selection_counts: &'a FxHashMap<String, u32>,
    pub artifact_capture: ArtifactCapture,
    pub depth: u16,
    pub refinement_step: u32,
    pub profiling: Option<Rc<RefCell<RefinementProfilingCollector>>>,
}

impl<F: TermCostFactory> SearchContext<'_, F> {
    pub fn term_cost(
        &self,
        context: &crate::policy::term_selection::context::TermCostContext,
        depth: u32,
    ) -> F {
        F::from_context(context, depth, self.term_config)
    }
    pub fn installable_expression(&self, expression: &TermExpr) -> Option<Term> {
        let term = expr_to_term(expression.clone());
        self.smt
            .make_unquantified_instance(term)
            .map(|instance| canonical_instantiation_key(instance.get_term()))
    }
}
