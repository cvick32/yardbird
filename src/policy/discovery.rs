//! Optional symbolic instance discovery, independent of matching and installation.
use std::collections::HashSet;

use smt2parser::concrete::Term;

use crate::{problem_context::ProblemContext, rule_matching::candidate::SymbolicInstance};

use super::effort::*;

pub(crate) struct DiscoveryContext<'a> {
    pub smt: &'a dyn ProblemContext,
    pub depth: u16,
    pub refinement_step: u32,
    pub model_version: u64,
    pub pending: &'a HashSet<Term>,
}

pub(crate) trait InstanceDiscovery {
    fn discover(&mut self, context: &DiscoveryContext<'_>)
        -> anyhow::Result<Vec<SymbolicInstance>>;
}

/// Give an optional discovery producer one turn per model, then use ordinary
/// search. Failure to propose an instance never means search is exhausted.
#[derive(Default)]
pub(crate) struct DiscoveryFirst {
    ordinary: DefaultEffort,
    attempted: Option<u64>,
    model: u64,
    handoff: bool,
}

impl ProofEffort for DiscoveryFirst {
    fn choose(&mut self, context: &EffortContext<'_>) -> EffortDecision {
        if self.handoff {
            return EffortDecision::ReturnToDriver;
        }
        if self.attempted != Some(context.model) {
            if let Some(operation) = context
                .operations
                .iter()
                .find(|o| o.kind == OperationKind::PolicyCandidates)
            {
                self.attempted = Some(context.model);
                return EffortDecision::Execute {
                    operation: operation.id,
                    allowance: WorkAllowance::default(),
                };
            }
        }
        self.ordinary.choose(context)
    }

    fn choose_binder_rule(&mut self, context: &BinderEffortContext<'_>) -> Option<usize> {
        self.ordinary.choose_binder_rule(context)
    }

    fn observe(&mut self, event: &EffortEvent<'_>) {
        match event {
            EffortEvent::NewProblem => {
                self.attempted = None;
                self.handoff = false;
            }
            EffortEvent::BeginPass { model, .. } => {
                self.model = *model;
                self.handoff = false;
            }
            EffortEvent::Completed {
                operation: OperationKind::PolicyCandidates,
                report,
            } => {
                self.attempted = Some(self.model);
                self.handoff = report.selected > 0;
                return;
            }
            _ => {}
        }
        self.ordinary.observe(event);
    }

    fn egraph_builder(
        &self,
    ) -> Box<dyn crate::theories::array::array_egraph_builder::ArrayEGraphBuilder> {
        self.ordinary.egraph_builder()
    }

    fn requires_property_cone(&self) -> bool {
        self.ordinary.requires_property_cone()
    }
}
