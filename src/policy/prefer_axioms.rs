//! A bounded prelude to the existing effort schedule. Classification is supplied
//! by lowering; this policy never inspects diagnostic provenance or formulas.
use super::effort::*;
use std::collections::{HashMap, HashSet};

#[derive(Default)]
pub(super) struct AxiomPrefix {
    model: Option<u64>,
    stage: usize,
    active: bool,
    pages: HashSet<(SearchPhase, usize)>,
    next_rule: HashMap<SearchPhase, usize>,
}

impl AxiomPrefix {
    pub fn active(&self) -> bool {
        self.active
    }

    pub fn choose(
        &mut self,
        context: &EffortContext<'_>,
        allowance: WorkAllowance,
    ) -> Option<EffortDecision> {
        let stages = [
            OperationKind::GuardedReads,
            OperationKind::ExpandArray,
            OperationKind::ArrayCandidates,
            OperationKind::Binder(SearchPhase::Witnesses),
            OperationKind::Binder(SearchPhase::Conflicts),
        ];
        while let Some(kind) = stages.get(self.stage) {
            // Existing array vocabulary can be searched without expanding it.
            if *kind == OperationKind::ExpandArray
                && context
                    .operations
                    .iter()
                    .any(|op| op.kind == OperationKind::ArrayCandidates)
            {
                self.stage += 1;
                continue;
            }
            if let Some(operation) = context.operations.iter().find(|op| op.kind == *kind) {
                self.active = true;
                return Some(EffortDecision::Execute {
                    operation: operation.id,
                    allowance,
                });
            }
            self.stage += 1;
        }
        None
    }

    pub fn choose_binder_rule(&self, context: &BinderEffortContext<'_>) -> Option<usize> {
        let next = self.next_rule.get(&context.phase).copied().unwrap_or(0);
        context
            .pending_rules
            .iter()
            .filter(|(id, name)| {
                context.background_rules.contains(name)
                    && !self.pages.contains(&(context.phase, *id))
            })
            .min_by_key(|(id, _)| {
                (id + context.rule_count - next % context.rule_count) % context.rule_count
            })
            .map(|(id, _)| *id)
    }

    /// Consume only our operation/page events. The ordinary policy still sees
    /// lifecycle events and resumes its untouched schedule after the prelude,
    /// even when the prelude selected instances. This avoids starving it.
    pub fn observe(&mut self, event: &EffortEvent<'_>) -> bool {
        match event {
            EffortEvent::NewProblem => *self = Self::default(),
            EffortEvent::BeginPass { model, .. } if self.model != Some(*model) => {
                self.model = Some(*model);
                self.stage = 0;
                self.active = false;
                self.pages.clear();
            }
            EffortEvent::BinderPage {
                phase,
                rule,
                rule_count,
                ..
            } if self.active => {
                self.pages.insert((*phase, *rule));
                self.next_rule.insert(*phase, (rule + 1) % rule_count);
                return true;
            }
            EffortEvent::Completed { .. } if self.active => {
                self.active = false;
                self.stage += 1;
                return true;
            }
            _ => {}
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prelude_is_bounded_even_when_productive_and_resets_for_new_models() {
        let mut policy = DefaultEffort::default()
            .with_prefer_axioms(true)
            .with_countermodel_refinement(true);
        let kinds = [
            OperationKind::GuardedReads,
            OperationKind::ArrayCandidates,
            OperationKind::Binder(SearchPhase::Witnesses),
            OperationKind::Binder(SearchPhase::Conflicts),
            OperationKind::CountermodelCandidates,
        ];
        for model in [1, 2] {
            policy.observe(&EffortEvent::BeginPass {
                model,
                depth: 2,
                refinement_step: 0,
            });
            let operations = kinds
                .iter()
                .enumerate()
                .map(|(index, kind)| EffortOperation {
                    id: OperationId {
                        model,
                        offer: 1,
                        index,
                    },
                    kind: *kind,
                    description: String::new(),
                })
                .collect::<Vec<_>>();
            let context = EffortContext {
                model,
                graph_version: 0,
                depth: 2,
                refinement_step: 0,
                pending_instances: 1,
                operations: &operations,
            };
            for operation in &operations {
                let EffortDecision::Execute {
                    operation: chosen, ..
                } = policy.choose(&context)
                else {
                    panic!("missing operation");
                };
                assert_eq!(chosen, operation.id);
                if let OperationKind::Binder(phase) = operation.kind {
                    let pending = [(0, "ordinary".into()), (1, "background".into())];
                    let background = HashSet::from(["background".into()]);
                    let binders = BinderEffortContext {
                        phase,
                        pending_rules: &pending,
                        rule_count: 2,
                        background_rules: &background,
                    };
                    assert_eq!(policy.choose_binder_rule(&binders), Some(1));
                    policy.observe(&EffortEvent::BinderPage {
                        phase,
                        rule: 1,
                        rule_count: 2,
                        report: &WorkReport::default(),
                    });
                    assert_eq!(
                        policy.choose_binder_rule(&binders),
                        None,
                        "only one page per preferred rule"
                    );
                }
                policy.observe(&EffortEvent::Completed {
                    operation: operation.kind,
                    report: &WorkReport {
                        selected: 1,
                        ..Default::default()
                    },
                });
            }
        }
    }
}
