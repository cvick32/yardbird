//! A bounded read-support prelude with ordinary guided search as fallback.
use super::effort::*;
use crate::theories::array::array_egraph_builder::ArrayEGraphBuilder;

pub struct ReadSupportEffort {
    ordinary: DefaultEffort,
    allowance: WorkAllowance,
    attempted_model: Option<u64>,
}
impl ReadSupportEffort {
    pub fn new(ordinary: DefaultEffort, allowance: WorkAllowance) -> Self {
        Self {
            ordinary,
            allowance,
            attempted_model: None,
        }
    }
}
impl ProofEffort for ReadSupportEffort {
    fn choose(&mut self, context: &EffortContext<'_>) -> EffortDecision {
        // Yield every eighth refinement even if the prelude remains productive.
        // Empty preludes fall through immediately, without changing rotation.
        if context.pending_instances == 0
            && context.refinement_step % 8 != 7
            && self.attempted_model != Some(context.model)
        {
            self.attempted_model = Some(context.model);
            if let Some(operation) = context
                .operations
                .iter()
                .find(|op| op.kind == OperationKind::ReadSupport)
            {
                return EffortDecision::Execute {
                    operation: operation.id,
                    allowance: self.allowance,
                };
            }
        }
        self.ordinary.choose(context)
    }
    fn choose_binder_rule(&mut self, context: &BinderEffortContext<'_>) -> Option<usize> {
        self.ordinary.choose_binder_rule(context)
    }
    fn observe(&mut self, event: &EffortEvent<'_>) {
        if matches!(event, EffortEvent::NewProblem) {
            self.attempted_model = None;
        }
        if matches!(event, EffortEvent::Completed { operation, report } if *operation == OperationKind::ReadSupport && report.selected == 0)
        {
            return;
        }
        self.ordinary.observe(event);
    }
    fn uses_countermodel_refinement(&self) -> bool {
        self.ordinary.uses_countermodel_refinement()
    }
    fn egraph_builder(&self) -> Box<dyn ArrayEGraphBuilder> {
        self.ordinary.egraph_builder()
    }
    fn requires_property_cone(&self) -> bool {
        self.ordinary.requires_property_cone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn choose(policy: &mut ReadSupportEffort, model: u64, step: u32) -> Option<OperationKind> {
        let operations = [
            OperationKind::ReadSupport,
            OperationKind::DiscoverDependencies,
            OperationKind::Binder(SearchPhase::Witnesses),
        ]
        .into_iter()
        .enumerate()
        .map(|(index, kind)| EffortOperation {
            id: OperationId {
                model,
                offer: 1,
                index,
            },
            kind,
            description: String::new(),
        })
        .collect::<Vec<_>>();
        match policy.choose(&EffortContext {
            model,
            graph_version: 0,
            depth: 0,
            refinement_step: step,
            pending_instances: 0,
            operations: &operations,
        }) {
            EffortDecision::Execute { operation, .. } => Some(operations[operation.index].kind),
            EffortDecision::ReturnToDriver => None,
            EffortDecision::Stop => panic!("grounding is not an exhaustion oracle"),
        }
    }
    fn begin(policy: &mut ReadSupportEffort, model: u64, step: u32) {
        policy.observe(&EffortEvent::BeginPass {
            model,
            depth: 0,
            refinement_step: step,
        });
    }
    #[test]
    fn read_support_fall_back_once_per_model_and_yield_every_eighth_refinement() {
        let mut policy = ReadSupportEffort::new(DefaultEffort::default(), WorkAllowance::default());
        begin(&mut policy, 1, 0);
        assert_eq!(choose(&mut policy, 1, 0), Some(OperationKind::ReadSupport));
        policy.observe(&EffortEvent::Completed {
            operation: OperationKind::ReadSupport,
            report: &WorkReport::default(),
        });
        assert_eq!(
            choose(&mut policy, 1, 0),
            Some(OperationKind::DiscoverDependencies)
        );
        begin(&mut policy, 1, 1);
        assert_eq!(
            choose(&mut policy, 1, 1),
            Some(OperationKind::DiscoverDependencies)
        );
        begin(&mut policy, 2, 7);
        assert_eq!(
            choose(&mut policy, 2, 7),
            Some(OperationKind::Binder(SearchPhase::Witnesses))
        );
        begin(&mut policy, 3, 8);
        assert_eq!(choose(&mut policy, 3, 8), Some(OperationKind::ReadSupport));
    }
    #[test]
    fn read_support_return_to_solver_after_a_productive_prelude() {
        let mut policy = ReadSupportEffort::new(DefaultEffort::default(), WorkAllowance::default());
        begin(&mut policy, 1, 0);
        choose(&mut policy, 1, 0);
        policy.observe(&EffortEvent::Completed {
            operation: OperationKind::ReadSupport,
            report: &WorkReport {
                selected: 1,
                ..Default::default()
            },
        });
        assert_eq!(choose(&mut policy, 1, 0), None);
    }
}
