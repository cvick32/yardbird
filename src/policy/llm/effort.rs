//! Symbolic-first bounded slices. Yield after each operation for driver deadlines;
//! a yield does not reset the model, symbolic cursor, or inference budget.
use super::LlmOptions;
use crate::policy::effort::*;

pub(super) struct SymbolicLlmEffort {
    ordinary: DefaultEffort,
    allowance: WorkAllowance,
    options: LlmOptions,
    model: Option<u64>,
    symbolic_left: usize,
    llm_left: usize,
    calls: usize,
    model_calls: usize,
    disabled: bool,
    yield_to_driver: bool,
    restart_ordinary: bool,
    symbolic_completed: usize,
    symbolic_examined: usize,
    last_symbolic: Option<OperationKind>,
}
impl SymbolicLlmEffort {
    pub fn new(options: &LlmOptions) -> Self {
        let allowance = WorkAllowance {
            binder_page_size: options.symbolic_match_work,
            binder_search_limit: options.symbolic_match_work,
            array_initial_limit: options.symbolic_match_work,
            array_rounds: 1,
            dependency_work: options.symbolic_dependency_work,
            dependency_demands: options.symbolic_dependency_work,
            dependency_paths: options.symbolic_dependency_work,
            dependency_links: options.symbolic_dependency_work,
            dependency_helpers: options.symbolic_dependency_work,
            vocabulary_work: options.symbolic_vocabulary_work,
            ..WorkAllowance::default()
        };
        Self {
            // Reserve the rest of the default eight-operation slice for
            // witnesses, guards, array expansion/search, and binder conflicts.
            // Dependency continuation must not consume the entire LLM prefix.
            ordinary: DefaultEffort::default()
                .with_allowance(allowance)
                .with_dependency_burst_limits(1, 1),
            allowance,
            options: options.clone(),
            model: None,
            symbolic_left: options.symbolic_operations,
            llm_left: 0,
            calls: 0,
            model_calls: 0,
            disabled: false,
            yield_to_driver: false,
            restart_ordinary: false,
            symbolic_completed: 0,
            symbolic_examined: 0,
            last_symbolic: None,
        }
    }
}
impl ProofEffort for SymbolicLlmEffort {
    fn discovery_feedback(&self) -> serde_json::Value {
        serde_json::json!({"scope":"current model", "completed_operations":self.symbolic_completed,
            "examined_substitutions":self.symbolic_examined,"last_operation":self.last_symbolic.map(|op|format!("{op:?}")),
            "meaning":"Symbolic search has not installed an instance for this model. Bounded unsuccessful search does not establish absence of a violated instance."})
    }
    fn allows_concrete_validation(&self) -> bool {
        false
    }
    fn choose(&mut self, context: &EffortContext<'_>) -> EffortDecision {
        if context.pending_instances > 0 || self.yield_to_driver {
            return EffortDecision::ReturnToDriver;
        }
        if self.disabled
            || self.calls >= self.options.llm_max_calls
            || self.model_calls >= self.options.llm_max_calls_per_model
        {
            log::info!(
                "symbolic-llm stopped: inference_disabled={}, run_calls={}/{}, model_calls={}/{}",
                self.disabled,
                self.calls,
                self.options.llm_max_calls,
                self.model_calls,
                self.options.llm_max_calls_per_model
            );
            return EffortDecision::Stop;
        }
        if self.symbolic_left > 0 {
            match self.ordinary.choose(context) {
                EffortDecision::Execute { operation, .. } => {
                    return EffortDecision::Execute {
                        operation,
                        allowance: self.allowance,
                    }
                }
                _ => {
                    self.symbolic_left = 0;
                    self.restart_ordinary = true;
                }
            }
        }
        if self.llm_left == 0 {
            self.llm_left = self.options.llm_attempts;
        }
        match context
            .operations
            .iter()
            .find(|o| o.kind == OperationKind::PolicyCandidates)
        {
            Some(op) => EffortDecision::Execute {
                operation: op.id,
                allowance: WorkAllowance {
                    discovery_calls: 1,
                    ..self.allowance
                },
            },
            None => EffortDecision::Stop,
        }
    }
    fn choose_binder_rule(&mut self, context: &BinderEffortContext<'_>) -> Option<usize> {
        self.ordinary.choose_binder_rule(context)
    }
    fn observe(&mut self, event: &EffortEvent<'_>) {
        match event {
            EffortEvent::NewProblem => {
                self.model = None;
                self.calls = 0;
                self.disabled = false;
                self.ordinary.observe(event);
            }
            EffortEvent::BeginPass { model, .. } => {
                self.yield_to_driver = false;
                if self.model != Some(*model) {
                    self.model = Some(*model);
                    self.model_calls = 0;
                    self.symbolic_completed = 0;
                    self.symbolic_examined = 0;
                    self.last_symbolic = None;
                    self.symbolic_left = self.options.symbolic_operations;
                    self.llm_left = 0;
                    self.restart_ordinary = false;
                    self.ordinary.observe(event);
                } else if self.restart_ordinary && self.symbolic_left > 0 {
                    self.restart_ordinary = false;
                    self.ordinary.observe(event);
                }
            }
            EffortEvent::Completed { operation, report } => {
                self.yield_to_driver = true;
                if *operation == OperationKind::PolicyCandidates {
                    self.calls += report.discovery_calls;
                    self.model_calls += report.discovery_calls;
                    self.disabled |= report.discovery_disabled;
                    self.llm_left = self.llm_left.saturating_sub(1);
                    if self.llm_left == 0 {
                        self.symbolic_left = self.options.symbolic_operations;
                        // Start a fresh bounded pass after the LLM turn. The
                        // prior slice may have ended exactly at Stage::Return;
                        // observing BeginPass preserves the search cursors but
                        // prevents an empty pass from immediately calling again.
                        self.restart_ordinary = true;
                    }
                } else {
                    self.symbolic_left = self.symbolic_left.saturating_sub(1);
                    self.symbolic_completed += 1;
                    self.symbolic_examined += report.examined_substitutions;
                    self.last_symbolic = Some(*operation);
                    self.ordinary.observe(event);
                }
            }
            _ => self.ordinary.observe(event),
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn quantifier_only_slices(continuable: bool) -> Vec<Vec<OperationKind>> {
        let options = LlmOptions {
            llm_max_calls_per_model: 3,
            ..Default::default()
        };
        let mut effort = SymbolicLlmEffort::new(&options);
        effort.observe(&EffortEvent::NewProblem);
        let operations = [
            OperationKind::DiscoverDependencies,
            OperationKind::DependencyRequest(0),
            OperationKind::DependencyRequest(1),
            OperationKind::DependencyRequest(2),
            OperationKind::Binder(SearchPhase::Witnesses),
            OperationKind::Binder(SearchPhase::TriggeredConflicts),
            OperationKind::Binder(SearchPhase::Conflicts),
            OperationKind::Binder(SearchPhase::Expand),
            OperationKind::PolicyCandidates,
        ]
        .into_iter()
        .enumerate()
        .map(|(index, kind)| EffortOperation {
            id: OperationId {
                model: 1,
                offer: 1,
                index,
            },
            kind,
            description: String::new(),
        })
        .collect::<Vec<_>>();
        let context = EffortContext {
            model: 1,
            graph_version: 1,
            depth: 0,
            refinement_step: 0,
            pending_instances: 0,
            operations: &operations,
        };
        let mut slices = Vec::new();
        let mut slice = Vec::new();
        // The coordinator offers exhausted directed requests too. No array
        // expansion can reopen dependency search on these inputs.
        for _ in 0..40 {
            effort.observe(&EffortEvent::BeginPass {
                model: 1,
                depth: 0,
                refinement_step: 0,
            });
            let EffortDecision::Execute { operation, .. } = effort.choose(&context) else {
                break;
            };
            let kind = operations[operation.index].kind;
            slice.push(kind);
            effort.observe(&EffortEvent::Completed {
                operation: kind,
                report: &WorkReport {
                    continuable: kind == OperationKind::DiscoverDependencies && continuable,
                    discovery_calls: usize::from(kind == OperationKind::PolicyCandidates),
                    ..Default::default()
                },
            });
            assert!(matches!(
                effort.choose(&context),
                EffortDecision::ReturnToDriver
            ));
            if kind == OperationKind::PolicyCandidates {
                slices.push(std::mem::take(&mut slice));
            }
        }
        assert_eq!(slices.len(), 3);
        // A new model must restart discovery and request rotation.
        effort.observe(&EffortEvent::BeginPass {
            model: 2,
            depth: 0,
            refinement_step: 1,
        });
        for expected in [
            OperationKind::DiscoverDependencies,
            OperationKind::DependencyRequest(0),
        ] {
            let EffortDecision::Execute { operation, .. } = effort.choose(&context) else {
                panic!("missing new-model work")
            };
            assert_eq!(operations[operation.index].kind, expected);
            effort.observe(&EffortEvent::Completed {
                operation: expected,
                report: &WorkReport::default(),
            });
            effort.observe(&EffortEvent::BeginPass {
                model: 2,
                depth: 0,
                refinement_step: 1,
            });
        }
        slices
    }

    #[test]
    fn quantifier_only_hybrid_resumes_continuable_dependency_discovery() {
        for slice in quantifier_only_slices(true) {
            assert!(
                slice.contains(&OperationKind::DiscoverDependencies),
                "{slice:?}"
            );
        }
    }

    #[test]
    fn quantifier_only_hybrid_rotates_requests_after_discovery_finishes() {
        for (index, slice) in quantifier_only_slices(false).iter().enumerate() {
            let requests = slice
                .iter()
                .filter_map(|kind| match kind {
                    OperationKind::DependencyRequest(i) => Some(*i),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(requests, vec![index], "{slice:?}");
            assert_eq!(
                slice.contains(&OperationKind::DiscoverDependencies),
                index == 0
            );
        }
    }
    #[test]
    fn hybrid_tries_binder_and_array_candidates_despite_continuable_dependencies() {
        let options = LlmOptions::default();
        let mut effort = SymbolicLlmEffort::new(&options);
        effort.observe(&EffortEvent::NewProblem);
        let begin = EffortEvent::BeginPass {
            model: 1,
            depth: 1,
            refinement_step: 0,
        };
        let mut sequence = Vec::new();
        let mut slices = Vec::new();
        let mut array_ready = false;
        for offer in 0..2 * (options.symbolic_operations + 1) {
            // Match the coordinator: dependency work remains continuable,
            // requests keep arriving, and array candidates require expansion.
            let mut kinds = vec![OperationKind::DiscoverDependencies];
            kinds.extend((0..32).map(OperationKind::DependencyRequest));
            kinds.extend([
                OperationKind::Binder(SearchPhase::Witnesses),
                OperationKind::Binder(SearchPhase::TriggeredConflicts),
                OperationKind::Binder(SearchPhase::Conflicts),
                OperationKind::Binder(SearchPhase::Expand),
                OperationKind::GuardedReads,
                OperationKind::ExpandArray,
                OperationKind::GrowVocabulary,
                OperationKind::PolicyCandidates,
            ]);
            if array_ready {
                kinds.push(OperationKind::ArrayCandidates);
            }
            let operations = kinds
                .into_iter()
                .enumerate()
                .map(|(index, kind)| EffortOperation {
                    id: OperationId {
                        model: 1,
                        offer: offer as u64,
                        index,
                    },
                    kind,
                    description: String::new(),
                })
                .collect::<Vec<_>>();
            effort.observe(&begin);
            let context = EffortContext {
                model: 1,
                graph_version: 1,
                depth: 1,
                refinement_step: 0,
                pending_instances: 0,
                operations: &operations,
            };
            let EffortDecision::Execute { operation, .. } = effort.choose(&context) else {
                panic!("expected a bounded operation");
            };
            let kind = operations[operation.index].kind;
            sequence.push(kind);
            if kind == OperationKind::PolicyCandidates {
                slices.push(std::mem::take(&mut sequence));
                if slices.len() == 2 {
                    break;
                }
            }
            array_ready |= kind == OperationKind::ExpandArray;
            effort.observe(&EffortEvent::Completed {
                operation: kind,
                report: &WorkReport {
                    continuable: true,
                    budget_exhausted: true,
                    discovery_calls: usize::from(kind == OperationKind::PolicyCandidates),
                    ..Default::default()
                },
            });
            assert!(matches!(
                effort.choose(&context),
                EffortDecision::ReturnToDriver
            ));
        }
        assert_eq!(
            slices.len(),
            2,
            "fallback must remain bounded on the same model"
        );
        for sequence in &slices {
            assert_eq!(sequence.last(), Some(&OperationKind::PolicyCandidates));
            assert!(
                sequence.contains(&OperationKind::Binder(SearchPhase::Witnesses)),
                "{sequence:?}"
            );
            assert!(
                sequence.contains(&OperationKind::Binder(SearchPhase::TriggeredConflicts)),
                "{sequence:?}"
            );
            assert!(
                sequence.contains(&OperationKind::ArrayCandidates),
                "{sequence:?}"
            );
            assert!(
                sequence
                    .iter()
                    .filter(|&&kind| kind == OperationKind::DiscoverDependencies)
                    .count()
                    <= 1
            );
            assert!(
                sequence
                    .iter()
                    .filter(|kind| matches!(kind, OperationKind::DependencyRequest(_)))
                    .count()
                    <= 1
            );
        }
    }

    #[test]
    fn symbolic_slices_preempt_continuable_search_and_retry_without_a_new_model() {
        let options = LlmOptions {
            symbolic_operations: 2,
            llm_attempts: 2,
            llm_max_calls_per_model: 3,
            ..Default::default()
        };
        let mut effort = SymbolicLlmEffort::new(&options);
        let operations = [
            OperationKind::DiscoverDependencies,
            OperationKind::DependencyRequest(0),
            OperationKind::PolicyCandidates,
        ]
        .into_iter()
        .enumerate()
        .map(|(index, kind)| EffortOperation {
            id: OperationId {
                model: 1,
                offer: 1,
                index,
            },
            kind,
            description: String::new(),
        })
        .collect::<Vec<_>>();
        let context = EffortContext {
            model: 1,
            graph_version: 1,
            depth: 0,
            refinement_step: 0,
            pending_instances: 0,
            operations: &operations,
        };
        effort.observe(&EffortEvent::NewProblem);
        let begin = EffortEvent::BeginPass {
            model: 1,
            depth: 0,
            refinement_step: 0,
        };
        effort.observe(&begin);
        let mut sequence = vec![];
        loop {
            let (op, allowance) = match effort.choose(&context) {
                EffortDecision::Execute {
                    operation,
                    allowance,
                } => (operations[operation.index].kind, allowance),
                EffortDecision::Stop => break,
                _ => panic!("unexpected yield before work"),
            };
            assert_eq!(allowance.binder_search_limit, options.symbolic_match_work);
            sequence.push(op);
            let report = WorkReport {
                continuable: true,
                discovery_calls: usize::from(op == OperationKind::PolicyCandidates),
                ..Default::default()
            };
            effort.observe(&EffortEvent::Completed {
                operation: op,
                report: &report,
            });
            assert!(matches!(
                effort.choose(&context),
                EffortDecision::ReturnToDriver
            ));
            effort.observe(&begin);
            assert!(sequence.len() < 12, "unbounded no-progress loop");
        }
        assert_eq!(
            sequence,
            vec![
                OperationKind::DiscoverDependencies,
                OperationKind::DependencyRequest(0),
                OperationKind::PolicyCandidates,
                OperationKind::PolicyCandidates,
                OperationKind::DiscoverDependencies,
                OperationKind::DependencyRequest(0),
                OperationKind::PolicyCandidates
            ]
        );
        assert_eq!(effort.calls, 3);
        assert!(!effort.allows_concrete_validation());
        // Per-model budget resets, the run budget does not.
        effort.observe(&EffortEvent::BeginPass {
            model: 2,
            depth: 0,
            refinement_step: 1,
        });
        assert_eq!(effort.model_calls, 0);
        assert_eq!(effort.calls, 3);
        assert!(matches!(
            effort.choose(&context),
            EffortDecision::Execute { .. }
        ));
    }
}
