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

/// Give a discovery producer one turn per model. Default mode falls back to
/// ordinary search; strict mode stops as inconclusive when no candidate remains.
#[derive(Default)]
pub(crate) struct DiscoveryFirst {
    ordinary: DefaultEffort,
    no_fallback: bool,
    attempted: Option<u64>,
    model: u64,
    handoff: bool,
    discovery_winners: Option<usize>,
}

impl DiscoveryFirst {
    pub(crate) fn with_no_fallback(mut self, no_fallback: bool) -> Self {
        self.no_fallback = no_fallback;
        self
    }

    pub(crate) fn with_discovery_winners(mut self, winners: usize) -> Self {
        self.discovery_winners = Some(winners.max(1));
        self
    }
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
                    allowance: WorkAllowance {
                        winners: self.discovery_winners.unwrap_or(1),
                        ..WorkAllowance::default()
                    },
                };
            }
        }
        if self.no_fallback {
            if context.pending_instances > 0 {
                EffortDecision::ReturnToDriver
            } else {
                EffortDecision::Stop
            }
        } else {
            self.ordinary.choose(context)
        }
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
