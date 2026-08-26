use std::{cell::RefCell, collections::HashSet, hash::Hash, mem, rc::Rc, time::Instant};

use log::{info, trace, warn};
use rustc_hash::FxHashMap;
use smt2parser::{concrete::Term, vmt::VMTModel};

use crate::{
    auxiliary_synthesis::{
        term_contains_auxiliary_symbol, ArrayConflictRecord, AuxSynthesisConfig, AuxTriggerState,
        AuxiliarySpec, SynthesisTrigger,
    },
    cost_functions::array::{ArrayCostContext, ArrayCostFactory},
    driver::{self},
    ic3ia::{call_ic3ia, ic3ia_output_contains_proof},
    instantiation_strategy::assertion_tracker::canonical_instantiation_key,
    profiling::{ArrayProfilingCollector, ProfilingRecord, ProfilingRunRecord},
    quantified_rule::{QuantifiedRuleCategory, TransitionGuardRule},
    theories::array::{
        array_axioms::{
            expr_to_term, generate_array_instantiation_candidates, ArrayExpr,
            ArrayInstantiationInstrumentation, ArrayInstantiationOptions, ArrayLanguage,
        },
        array_dataflow::{build_property_cone, PropertyCone},
        array_egraph_builder::{
            ArrayEGraphBuildStage, ArrayEGraphBuildStep, ArrayEGraphBuilder, FullEGraphBuilder,
        },
        array_rule_instantiator::ArrayArtifactCapture,
        array_term_extractor::{ArrayTermExtractor, ArrayTermExtractorOptions},
        candidate_scope::CandidateScope,
        instantiation_candidate::{InstantiationBatch, InstantiationCandidate},
        transition_guard_instantiator::{generate_guard_candidates, supports_transition_guard},
    },
    theory_support::{ArrayTheorySupport, TheorySupport},
    training::{AbstractInstantiationRecord, DecisionRecord},
    ProofLoopResult,
};

use super::{ProofAction, ProofStrategy};

fn trace_conflicts_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

fn trace_instantiations_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

/// Global state carried across different BMC depths
pub struct Abstract<F>
where
    F: ArrayCostFactory,
{
    _bmc_depth: u16,
    run_ic3ia: bool,
    cost_config: F::Config,
    discovered_array_types: Vec<(String, String)>,
    transition_guard_rules: Vec<TransitionGuardRule>,
    decision_data: Vec<DecisionRecord>,
    abstract_instantiations: Vec<AbstractInstantiationRecord>,
    term_selection_counts: FxHashMap<String, u32>,
    term_selection_decisions: FxHashMap<String, String>,
    artifact_capture: ArrayArtifactCapture,
    aux_config: AuxSynthesisConfig,
    aux_trigger_state: AuxTriggerState,
    pending_aux_specs: Vec<AuxiliarySpec>,
    installed_aux_conflicts: HashSet<String>,
    aux_covered_term_hashes: HashSet<String>,
    profile: bool,
    profiling_records: Vec<ProfilingRecord>,
    egraph_builder: Box<dyn ArrayEGraphBuilder>,
    cone_attempted_depths: HashSet<u16>,
    property_cone: PropertyCone,
    preprocess_exact_read_after_write: bool,
}

impl<F> Abstract<F>
where
    F: ArrayCostFactory,
{
    pub fn new(
        bmc_depth: u16,
        run_ic3ia: bool,
        cost_config: F::Config,
        aux_config: AuxSynthesisConfig,
        profile: bool,
    ) -> Self {
        let capture_conflicts = !aux_config.is_off();
        Self {
            _bmc_depth: bmc_depth,
            run_ic3ia,
            aux_config,
            cost_config,
            discovered_array_types: vec![],
            transition_guard_rules: vec![],
            decision_data: vec![],
            abstract_instantiations: vec![],
            term_selection_counts: FxHashMap::default(),
            term_selection_decisions: FxHashMap::default(),
            artifact_capture: ArrayArtifactCapture {
                conflicts: capture_conflicts,
                ..ArrayArtifactCapture::default()
            },
            aux_trigger_state: AuxTriggerState::default(),
            pending_aux_specs: vec![],
            installed_aux_conflicts: HashSet::new(),
            aux_covered_term_hashes: HashSet::new(),
            profile,
            profiling_records: vec![],
            egraph_builder: Box::<FullEGraphBuilder>::default(),
            cone_attempted_depths: HashSet::new(),
            property_cone: PropertyCone::default(),
            preprocess_exact_read_after_write: false,
        }
    }

    pub fn with_artifact_capture(mut self, mut artifact_capture: ArrayArtifactCapture) -> Self {
        artifact_capture.conflicts |= !self.aux_config.is_off();
        self.artifact_capture = artifact_capture;
        self
    }

    pub fn with_egraph_builder(mut self, egraph_builder: Box<dyn ArrayEGraphBuilder>) -> Self {
        self.egraph_builder = egraph_builder;
        self
    }

    pub fn with_exact_read_after_write_preprocessing(mut self, enabled: bool) -> Self {
        self.preprocess_exact_read_after_write = enabled;
        self
    }
}

#[cfg(test)]
mod tests {
    use smt2parser::vmt::quantified_instantiator::UnquantifiedInstantiator;

    use super::*;
    use crate::{
        instantiation_provenance::InstantiationProvenance,
        quantified_rule::{ArrayAxiomKind, QuantifiedRule},
        theories::array::instantiation_candidate::{CandidateGroup, SelectionHistoryDecision},
    };

    fn candidate(expression: ArrayExpr) -> InstantiationCandidate {
        InstantiationCandidate {
            rule: QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, "Int", "Int"),
            expression,
            cost: 0,
            provenance: InstantiationProvenance::new("test".to_string(), vec![]),
            selected: false,
            decisions: vec![],
            selection_history: vec![],
            abstract_instantiation: None,
            conflict: None,
            group: CandidateGroup::MatchRoot(egg::Id::from(0)),
        }
    }

    fn normalized_key(candidate: &InstantiationCandidate) -> Option<Term> {
        UnquantifiedInstantiator::rewrite_unquantified(
            expr_to_term(candidate.expression.clone()),
            vec![],
        )
        .map(|instance| canonical_instantiation_key(instance.get_term()))
    }

    #[test]
    fn full_search_skips_known_group() {
        let installed = candidate("(= (Read Int Int a@0 i@0) 0)".parse().unwrap());
        let mut known_winner = candidate("(= (Read Int Int a@2 i@2) 0)".parse().unwrap());
        known_winner
            .selection_history
            .push(SelectionHistoryDecision {
                decision_key: "known-winner".to_string(),
                chosen_term_hash: "winner-term".to_string(),
            });
        let mut alternative = candidate("(= (Read Int Int a@2 i@2) 1)".parse().unwrap());
        alternative.cost = 1;
        alternative
            .selection_history
            .push(SelectionHistoryDecision {
                decision_key: "alternative".to_string(),
                chosen_term_hash: "alternative-term".to_string(),
            });
        let mut independent = candidate("(= (Read Int Int b@2 j@2) 0)".parse().unwrap());
        independent.group = CandidateGroup::MatchRoot(egg::Id::from(1));
        let expected = independent.expression.clone();
        let known = HashSet::from([normalized_key(&installed).unwrap()]);
        let mut batch = InstantiationBatch {
            candidates: vec![known_winner, alternative, independent],
        };

        let rejected = select_novel_candidates(
            CandidateScope::AllCandidates,
            &mut batch,
            &known,
            normalized_key,
        );

        assert_eq!(rejected, 1);
        assert_eq!(
            batch.selected().map(|c| &c.expression).collect::<Vec<_>>(),
            vec![&expected],
        );
        assert_eq!(known.len(), 1);
        assert_eq!(
            batch
                .candidates
                .iter()
                .flat_map(|c| &c.selection_history)
                .map(|decision| decision.chosen_term_hash.as_str())
                .collect::<Vec<_>>(),
            vec!["winner-term"],
        );
    }

    #[test]
    fn full_losers_do_not_deduplicate() {
        let winner = candidate("(= (Read Int Int a@2 i@2) 0)".parse().unwrap());
        let mut loser = candidate("(= (Read Int Int b@2 j@2) 0)".parse().unwrap());
        loser.cost = 1;
        let mut independent = candidate("(= (Read Int Int b@4 j@4) 0)".parse().unwrap());
        independent.group = CandidateGroup::MatchRoot(egg::Id::from(1));
        let expected = vec![winner.expression.clone(), independent.expression.clone()];
        let mut batch = InstantiationBatch {
            candidates: vec![winner, loser, independent],
        };

        let rejected = select_novel_candidates(
            CandidateScope::AllCandidates,
            &mut batch,
            &HashSet::new(),
            normalized_key,
        );

        assert_eq!(rejected, 0);
        assert_eq!(
            batch
                .selected()
                .map(|c| c.expression.clone())
                .collect::<Vec<_>>(),
            expected,
        );
    }

    #[test]
    fn other_policies_skip_known() {
        for (scope, rule) in [
            (
                CandidateScope::SourceGroundedOnly,
                QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, "Int", "Int"),
            ),
            (
                CandidateScope::SourceGroundedOnly,
                QuantifiedRule::transition_guard("guard", 0),
            ),
            (
                CandidateScope::AllCandidates,
                QuantifiedRule::transition_guard("guard", 0),
            ),
        ] {
            let mut known_winner = candidate("(= (Read Int Int a@2 i@2) 0)".parse().unwrap());
            if rule.category() == QuantifiedRuleCategory::TransitionGuard {
                known_winner.group = CandidateGroup::Rule;
            }
            known_winner.rule = rule.clone();
            let mut alternative = candidate("(= (Read Int Int a@2 i@2) 1)".parse().unwrap());
            alternative.group = known_winner.group;
            alternative.rule = rule;
            alternative.cost = 1;
            let expected = alternative.expression.clone();
            let known = HashSet::from([normalized_key(&known_winner).unwrap()]);
            let mut batch = InstantiationBatch {
                candidates: vec![known_winner, alternative],
            };

            let rejected = select_novel_candidates(scope, &mut batch, &known, normalized_key);

            assert_eq!(rejected, 1);
            assert_eq!(
                batch.selected().map(|c| &c.expression).collect::<Vec<_>>(),
                vec![&expected],
            );
        }
    }

    #[test]
    fn shifted_copies_of_an_instantiation_are_duplicate_after_normalization() {
        let installed = "(=> (not (= i@12 i@11)) (= (Read Int Int a@11 i@12) 0))"
            .parse::<ArrayExpr>()
            .unwrap();
        let expression = "(=> (not (= i@5 i@4)) (= (Read Int Int a@4 i@5) 0))"
            .parse::<ArrayExpr>()
            .unwrap();
        let mut batch = InstantiationBatch {
            candidates: vec![candidate(expression)],
        };
        let known = HashSet::from([UnquantifiedInstantiator::rewrite_unquantified(
            expr_to_term(installed),
            vec![],
        )
        .unwrap()
        .get_term()
        .clone()]);

        let duplicates = select_novel_candidates(
            CandidateScope::SourceGroundedOnly,
            &mut batch,
            &known,
            |candidate| {
                UnquantifiedInstantiator::rewrite_unquantified(
                    expr_to_term(candidate.expression.clone()),
                    vec![],
                )
                .map(|instance| instance.get_term().clone())
            },
        );

        assert_eq!(duplicates, 1);
        assert!(batch.candidates.is_empty());
        assert_eq!(known.len(), 1);
    }

    #[test]
    fn reversed_equalities_are_duplicate_before_whole_candidate_selection() {
        let installed: ArrayExpr = "(= (Read Int Int a@0 i@0) 0)".parse().unwrap();
        let reversed: ArrayExpr = "(= 0 (Read Int Int a@0 i@0))".parse().unwrap();
        let mut batch = InstantiationBatch {
            candidates: vec![candidate(reversed)],
        };
        let installed =
            UnquantifiedInstantiator::rewrite_unquantified(expr_to_term(installed), vec![])
                .unwrap();
        let known = HashSet::from([canonical_instantiation_key(installed.get_term())]);

        let duplicates = select_novel_candidates(
            CandidateScope::SourceGroundedOnly,
            &mut batch,
            &known,
            normalized_key,
        );

        assert_eq!(duplicates, 1);
        assert!(batch.candidates.is_empty());
    }

    #[test]
    fn only_axioms_false_in_the_current_model_remain_eligible() {
        let satisfied: ArrayExpr = "(= (Read Int Int A i) v)".parse().unwrap();
        let violated: ArrayExpr = "(= (Read Int Int B j) w)".parse().unwrap();
        let mut batch = InstantiationBatch {
            candidates: vec![candidate(satisfied), candidate(violated.clone())],
        };

        let rejected =
            filter_model_candidates(CandidateScope::SourceGroundedOnly, &mut batch, |term| {
                Ok(if term.to_string().contains("Read_Int_Int A") {
                    "true".to_string()
                } else {
                    "false".to_string()
                })
            })
            .unwrap();

        assert_eq!(rejected, 1);
        assert_eq!(batch.candidates.len(), 1);
        assert_eq!(batch.candidates[0].expression, violated);
    }

    #[test]
    fn full_search_keeps_egraph_conflicts_even_when_the_formula_is_model_satisfied() {
        let expression: ArrayExpr = "(= (Read Int Int A i) v)".parse().unwrap();
        let mut guard = candidate("(=> guard body)".parse().unwrap());
        guard.rule = QuantifiedRule::transition_guard("guard", 0);
        guard.group = CandidateGroup::Rule;
        let mut source_batch = InstantiationBatch {
            candidates: vec![candidate(expression.clone())],
        };
        let mut full_batch = InstantiationBatch {
            candidates: vec![candidate(expression.clone()), guard],
        };

        let source_rejected = filter_model_candidates(
            CandidateScope::SourceGroundedOnly,
            &mut source_batch,
            |_| Ok("true".to_string()),
        )
        .unwrap();
        let full_rejected =
            filter_model_candidates(CandidateScope::AllCandidates, &mut full_batch, |_| {
                Ok("true".to_string())
            })
            .unwrap();

        assert_eq!(source_rejected, 1);
        assert!(source_batch.candidates.is_empty());
        assert_eq!(full_rejected, 1);
        assert_eq!(full_batch.candidates.len(), 1);
        assert_eq!(full_batch.candidates[0].expression, expression);
    }

    #[test]
    fn model_filter_reuses_implication_guards() {
        let first: ArrayExpr = "(=> guard (= x y))".parse().unwrap();
        let second: ArrayExpr = "(=> guard (= a b))".parse().unwrap();
        let violated: ArrayExpr = "(= x y)".parse().unwrap();
        let mut batch = InstantiationBatch {
            candidates: vec![
                candidate(first),
                candidate(second),
                candidate(violated.clone()),
            ],
        };
        let mut evaluated = Vec::new();

        let rejected =
            filter_model_candidates(CandidateScope::SourceGroundedOnly, &mut batch, |term| {
                evaluated.push(term.to_string());
                Ok("false".to_string())
            })
            .unwrap();

        assert_eq!(rejected, 2);
        assert_eq!(batch.candidates.len(), 1);
        assert_eq!(batch.candidates[0].expression, violated);
        assert_eq!(evaluated, vec!["guard", "(= x y)"]);
    }
}

fn egraph_node_count<N>(egraph: &egg::EGraph<ArrayLanguage, N>) -> usize
where
    N: egg::Analysis<ArrayLanguage>,
{
    egraph.classes().map(|class| class.nodes.len()).sum()
}

#[derive(Clone, Copy, Debug)]
struct CandidateSummary {
    selected_candidates: usize,
    conflicts: usize,
}

/// State for the inner refinement looop
pub struct ArrayRefinementState {
    pub depth: u16,
    pub egraph: egg::EGraph<ArrayLanguage, ()>,
    pub candidates: Vec<InstantiationCandidate>,
    pub array_types: Vec<(String, String)>,
    pub(crate) egraph_builder: Box<dyn ArrayEGraphBuilder>,
}

impl<F> ProofStrategy<'_, ArrayRefinementState> for Abstract<F>
where
    F: ArrayCostFactory + 'static,
{
    fn get_theory_support(&self) -> Box<dyn TheorySupport> {
        Box::new(ArrayTheorySupport::new(self.discovered_array_types.clone()))
    }

    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        let (model, herbrand_witnesses) = model.herbrandize_universal_property();
        if herbrand_witnesses > 0 {
            info!("Herbrandized universal property with {herbrand_witnesses} witness constants");
        }
        let (abstracted_model, discovered_types) =
            model.abstract_array_theory_with_preprocessing(self.preprocess_exact_read_after_write);
        let supported_rules = abstracted_model
            .get_transition_guards()
            .into_iter()
            .enumerate()
            .map(|(ordinal, guard)| TransitionGuardRule::from_parsed(guard, ordinal))
            .filter(supports_transition_guard)
            .collect::<Vec<_>>();
        let selected_guards = supported_rules
            .iter()
            .map(|rule| rule.parsed().clone())
            .collect::<Vec<_>>();
        let (abstracted_model, removed_guards) =
            abstracted_model.abstract_transition_guards(&selected_guards);
        self.transition_guard_rules = supported_rules
            .into_iter()
            .filter(|rule| removed_guards.contains(rule.parsed()))
            .collect();
        if !self.transition_guard_rules.is_empty() {
            info!(
                "Abstracted {} quantified transition guard(s) for Yardbird instantiation",
                self.transition_guard_rules.len()
            );
        }
        self.property_cone = if self.egraph_builder.requires_property_cone() {
            build_property_cone(&abstracted_model)
        } else {
            PropertyCone::default()
        };
        self.discovered_array_types = discovered_types;
        abstracted_model
        //     .abstract_constants_over(self.bmc_depth)
    }

    fn preprocess_exact_read_after_write(&self) -> bool {
        self.preprocess_exact_read_after_write
    }

    fn setup(
        &mut self,
        smt: &dyn crate::problem_context::ProblemContext,
        depth: u16,
    ) -> driver::Result<ArrayRefinementState> {
        let egraph = egg::EGraph::new(());
        let egraph_builder = if self.egraph_builder.requires_property_cone()
            && !self.cone_attempted_depths.insert(depth)
        {
            Box::<FullEGraphBuilder>::default()
        } else {
            self.egraph_builder.clone()
        };
        // Use discovered_array_types if available (VMT mode via configure_model),
        // otherwise get from ProblemContext (SMTLIB mode)
        let array_types = if self.discovered_array_types.is_empty() {
            smt.get_array_types()
        } else {
            self.discovered_array_types.clone()
        };
        Ok(ArrayRefinementState {
            depth,
            egraph,
            candidates: vec![],
            array_types,
            egraph_builder,
        })
    }

    fn unsat(
        &mut self,
        state: &mut ArrayRefinementState,
        _solver: &dyn crate::problem_context::ProblemContext,
    ) -> driver::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut ArrayRefinementState,
        smt: &dyn crate::problem_context::ProblemContext,
        refinement_step: u32,
    ) -> driver::Result<ProofAction> {
        if trace_conflicts_enabled() {
            trace!(
                "[yardbird::conflict-trace] sat depth={} refinement_step={} eclasses_before={}",
                state.depth,
                refinement_step,
                state.egraph.number_of_classes()
            );
        }
        if !smt.has_model() {
            return Err(anyhow::anyhow!("No solver model available for SAT instance").into());
        }
        let profiling = self.profile.then(|| {
            Rc::new(RefCell::new(ArrayProfilingCollector::new(
                "array_refinement",
                Some(state.depth),
                Some(refinement_step),
                state.array_types.clone(),
            )))
        });
        if let Some(profiling) = &profiling {
            profiling.borrow_mut().set_egraph_before_update(
                state.egraph.number_of_classes(),
                egraph_node_count(&state.egraph),
            );
        }
        loop {
            let build_start = Instant::now();
            let build_step = state.egraph_builder.expand(
                &mut state.egraph,
                smt,
                &self.property_cone,
                state.depth,
            )?;
            let expansion = match build_step {
                ArrayEGraphBuildStep::Expanded(expansion) => expansion,
                ArrayEGraphBuildStep::Exhausted => {
                    self.finish_profiling_record(profiling);
                    return Ok(ProofAction::ValidateConcreteCounterexample);
                }
            };
            if let Some(profiling) = &profiling {
                let mut profiling = profiling.borrow_mut();
                profiling.record_timing("egraph_build", build_start.elapsed());
                profiling.add_counter("egraph_build_stages", 1);
                profiling.add_counter(
                    match expansion.stage {
                        ArrayEGraphBuildStage::Cone => "egraph_build_cone_stages",
                        ArrayEGraphBuildStage::Full => "egraph_build_full_stages",
                    },
                    1,
                );
                profiling.add_counter(
                    "egraph_build_newly_admitted_subterms",
                    expansion.newly_admitted_subterms as u64,
                );
                profiling.add_counter(
                    "egraph_build_demand_frontier_sites",
                    expansion.demand_frontier_sites as u64,
                );
                profiling.set_egraph_after_update(
                    state.egraph.number_of_classes(),
                    egraph_node_count(&state.egraph),
                );
            }

            let cost_factory_start = Instant::now();
            let candidate_catalog = if expansion.candidate_scope.tracks_provenance() {
                smt.get_array_candidate_catalog()
            } else {
                crate::problem_context::ArrayCandidateCatalog::default()
            };
            let cost_context =
                ArrayCostContext::from_problem(smt, &candidate_catalog, expansion.candidate_scope);
            let cost_fn = F::from_context(&cost_context, state.depth as u32, &self.cost_config);
            if let Some(profiling) = &profiling {
                profiling
                    .borrow_mut()
                    .record_timing("cost_factory", cost_factory_start.elapsed());
            }

            let known_instantiations = smt
                .get_instantiations()
                .into_iter()
                .map(|term| canonical_instantiation_key(&term))
                .collect::<HashSet<_>>();

            let instantiation_start = Instant::now();
            let mut candidate_batch = InstantiationBatch::default();
            if !self.transition_guard_rules.is_empty() && state.depth > 0 {
                let guard_extractor = ArrayTermExtractor::new(
                    &state.egraph,
                    cost_fn.clone(),
                    ArrayTermExtractorOptions {
                        candidate_catalog: candidate_catalog.clone(),
                        candidate_scope: expansion.candidate_scope,
                        refinement_step,
                        selection_counts: self.term_selection_counts.clone(),
                        depth: state.depth,
                        profiling: None,
                    },
                );

                for rule in &self.transition_guard_rules {
                    candidate_batch.extend(generate_guard_candidates(
                        rule,
                        &state.egraph,
                        &guard_extractor,
                        cost_fn.clone(),
                        state.depth,
                        smt,
                    ));
                }
            }

            let array_candidates = generate_array_instantiation_candidates(
                &state.egraph,
                cost_fn.clone(),
                &state.array_types,
                ArrayInstantiationOptions {
                    candidate_catalog: candidate_catalog.clone(),
                    candidate_scope: expansion.candidate_scope,
                    refinement_step,
                    selection_counts: self.term_selection_counts.clone(),
                    depth: state.depth,
                    instrumentation: ArrayInstantiationInstrumentation {
                        artifact_capture: self.artifact_capture,
                        profiling: profiling.clone(),
                    },
                },
            );
            candidate_batch.extend(array_candidates.candidates);
            let generated_by_rule = count_candidates_by_rule(&candidate_batch);

            let rejected_model =
                filter_model_candidates(expansion.candidate_scope, &mut candidate_batch, |term| {
                    smt.eval_to_string(term)
                })?;
            let rejected_known = select_novel_candidates(
                expansion.candidate_scope,
                &mut candidate_batch,
                &known_instantiations,
                |candidate| self.installable_expression(smt, &candidate.expression),
            );
            record_candidate_counts(&profiling, generated_by_rule, &candidate_batch);

            if let Some(profiling) = &profiling {
                let mut profiling = profiling.borrow_mut();
                profiling.add_counter(
                    "model_satisfied_instantiations_filtered",
                    rejected_model as u64,
                );
                profiling.add_counter(
                    "duplicate_or_uninstallable_instantiations_filtered",
                    rejected_known as u64,
                );
            }

            let summary = self.absorb_candidates(state, smt, candidate_batch, refinement_step);

            if let Some(profiling) = &profiling {
                profiling
                    .borrow_mut()
                    .record_timing("instantiation_total", instantiation_start.elapsed());
            }

            if trace_conflicts_enabled() {
                let selected_guards = state
                    .candidates
                    .iter()
                    .filter(|candidate| {
                        candidate.rule.category() == QuantifiedRuleCategory::TransitionGuard
                    })
                    .count();
                let selected_arrays = state.candidates.len().saturating_sub(selected_guards);
                trace!(
                    "[yardbird::conflict-trace] sat depth={} refinement_step={} build_stage={} selected_guards={} selected_arrays={} conflicts={}",
                    state.depth,
                    refinement_step,
                    expansion.stage.as_str(),
                    selected_guards,
                    selected_arrays,
                    summary.conflicts,
                );
            }
            if summary.selected_candidates > 0 {
                self.finish_profiling_record(profiling);
                return Ok(ProofAction::Continue);
            }
        }
    }

    #[allow(clippy::unnecessary_fold)]
    fn finish(
        &mut self,
        state: ArrayRefinementState,
        smt: &mut dyn crate::problem_context::ProblemContext,
    ) -> driver::Result<()> {
        let trace_instantiations = trace_instantiations_enabled();
        if !self.pending_aux_specs.is_empty() {
            let specs = mem::take(&mut self.pending_aux_specs);
            info!("AUX-SYNTH installing {} auxiliary specs", specs.len());
            smt.install_auxiliary_specs(specs)?;
        }
        for candidate in state.candidates {
            let expression = candidate.expression;
            let provenance = candidate.provenance;
            let term_hash = crate::training::canonical_term_hash(&expression);
            let term = expr_to_term(expression);
            let quantifier_kind = candidate.rule.category();
            if self.aux_covered_term_hashes.contains(&term_hash) {
                info!("AUX-SYNTH skipped aux-covered {quantifier_kind:#?} instantiation");
                continue;
            }
            if term_contains_auxiliary_symbol(&term) {
                info!("AUX-SYNTH skipped {quantifier_kind:#?} instantiation containing auxiliary symbols");
                continue;
            }

            let abstract_id = provenance.abstract_instantiation_id().to_string();
            if trace_instantiations {
                trace!(
                    "[yardbird::inst-trace] {quantifier_kind:#?} abstract-hash={term_hash} abstract-id={abstract_id} abstract-term={term} substitution={:?}",
                    provenance.relative_substitution(),
                );
            }

            let Some(request) = smt.make_provenanced_unquantified_instance(term, provenance) else {
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] {quantifier_kind:#?} rewrite-none abstract-id={abstract_id}"
                    );
                }
                continue;
            };
            let result = smt.add_instantiation(request);
            self.record_installation_outcome(&abstract_id, result);
            if trace_instantiations {
                trace!(
                    "[yardbird::inst-trace] {quantifier_kind:#?} add-result abstract-id={abstract_id} abstract-added={} solver-assertions-added={} indexed-deduplicated={} helper-deduplicated={}",
                    result.abstract_instance_added,
                    result.solver_assertions_added(),
                    result.indexed_assertions_deduplicated,
                    result.helper_assertions_deduplicated,
                );
            }
        }

        Ok(())
    }

    fn take_logging_artifacts(
        &mut self,
    ) -> (Vec<DecisionRecord>, Vec<AbstractInstantiationRecord>) {
        (
            mem::take(&mut self.decision_data),
            mem::take(&mut self.abstract_instantiations),
        )
    }

    fn take_profiling_records(&mut self) -> Vec<ProfilingRecord> {
        mem::take(&mut self.profiling_records)
    }

    fn result(
        &mut self,
        vmt_model: &mut VMTModel,
        smt: &dyn crate::problem_context::ProblemContext,
    ) -> ProofLoopResult {
        for instantiation_term in &smt.get_instantiations() {
            vmt_model.add_instantiation(instantiation_term);
        }
        let found_proof = if self.run_ic3ia {
            match call_ic3ia(vmt_model.clone()) {
                Ok(out) => {
                    info!("IC3IA OUT: {out}");
                    ic3ia_output_contains_proof(out)
                }
                Err(_) => false,
            }
        } else {
            false
        };
        ProofLoopResult {
            model: Some(vmt_model.clone()),
            used_instances: mem::take(&mut smt.get_instantiations()),
            total_instantiations_added: smt.get_number_instantiations_added(),
            total_refinement_steps: 0,
            solver_statistics: smt.get_solver_statistics(),
            counterexample: false,
            found_proof,
            unsat_core: None, // VMT mode unsat core tracked separately via dump-unsat-core
            decision_data: mem::take(&mut self.decision_data),
            abstract_instantiations: mem::take(&mut self.abstract_instantiations),
            indexed_instantiations: vec![],
            unsat_events: vec![],
            auxiliary_records: smt.get_auxiliary_records(),
            profiling: ProfilingRunRecord::default(),
        }
    }
}

fn count_candidates_by_rule(batch: &InstantiationBatch) -> FxHashMap<String, usize> {
    let mut counts = FxHashMap::default();
    for candidate in &batch.candidates {
        *counts.entry(candidate.rule.name().to_string()).or_default() += 1;
    }
    counts
}

fn record_candidate_counts(
    profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
    generated_by_rule: FxHashMap<String, usize>,
    batch: &InstantiationBatch,
) {
    let Some(profiling) = profiling else {
        return;
    };
    let mut selected_by_rule = FxHashMap::<String, usize>::default();
    for candidate in batch.selected() {
        *selected_by_rule
            .entry(candidate.rule.name().to_string())
            .or_default() += 1;
    }

    let mut profiling = profiling.borrow_mut();
    for (rule_name, generated) in generated_by_rule {
        let selected = selected_by_rule
            .get(&rule_name)
            .copied()
            .unwrap_or_default();
        profiling.record_rule_candidates(&rule_name, generated, selected);
    }
}

fn select_novel_candidates<K>(
    scope: CandidateScope,
    batch: &mut InstantiationBatch,
    known: &HashSet<K>,
    mut normalize: impl FnMut(&InstantiationCandidate) -> Option<K>,
) -> usize
where
    K: Eq + Hash,
{
    let mut seen = HashSet::new();
    batch.select(scope, |candidate| {
        let Some(normalized) = normalize(candidate) else {
            return false;
        };
        !known.contains(&normalized) && seen.insert(normalized)
    })
}

fn filter_model_candidates(
    scope: CandidateScope,
    batch: &mut InstantiationBatch,
    mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
) -> anyhow::Result<usize> {
    let before = batch.candidates.len();
    let mut eligible = Vec::with_capacity(before);
    let mut evaluations = FxHashMap::<String, String>::default();
    for candidate in mem::take(&mut batch.candidates) {
        let requires_model_violation = candidate.rule.category()
            == QuantifiedRuleCategory::TransitionGuard
            || scope.requires_model_violation();
        if !requires_model_violation {
            eligible.push(candidate);
            continue;
        }
        let term = expr_to_term(candidate.expression.clone());
        if model_value(&term, &mut evaluate, &mut evaluations)?.trim() == "false" {
            eligible.push(candidate);
        }
    }
    let rejected = before - eligible.len();
    batch.candidates = eligible;
    Ok(rejected)
}

fn model_value(
    term: &Term,
    evaluate: &mut impl FnMut(&Term) -> anyhow::Result<String>,
    cache: &mut FxHashMap<String, String>,
) -> anyhow::Result<String> {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return cached_model_value(term, evaluate, cache);
    };
    if qual_identifier.get_name() != "=>" || arguments.len() != 2 {
        return cached_model_value(term, evaluate, cache);
    }

    match cached_model_value(&arguments[0], evaluate, cache)?.trim() {
        "false" => Ok("true".to_string()),
        "true" => cached_model_value(&arguments[1], evaluate, cache),
        _ => cached_model_value(term, evaluate, cache),
    }
}

fn cached_model_value(
    term: &Term,
    evaluate: &mut impl FnMut(&Term) -> anyhow::Result<String>,
    cache: &mut FxHashMap<String, String>,
) -> anyhow::Result<String> {
    let key = term.to_string();
    if let Some(value) = cache.get(&key) {
        return Ok(value.clone());
    }
    let value = evaluate(term)?;
    cache.insert(key, value.clone());
    Ok(value)
}

impl<F> Abstract<F>
where
    F: ArrayCostFactory + 'static,
{
    fn record_installation_outcome(
        &mut self,
        abstract_instantiation_id: &str,
        result: crate::instantiation_provenance::InstantiationInstallResult,
    ) {
        let Some(record) = self
            .abstract_instantiations
            .iter_mut()
            .find(|record| record.abstract_instantiation_id == abstract_instantiation_id)
        else {
            return;
        };
        record.indexed_assertions_attempted += result.indexed_assertions_attempted;
        record.indexed_assertions_added += result.indexed_assertions_added;
        record.indexed_assertions_deduplicated += result.indexed_assertions_deduplicated;
        record.helper_assertions_attempted += result.helper_assertions_attempted;
        record.helper_assertions_added += result.helper_assertions_added;
        record.helper_assertions_deduplicated += result.helper_assertions_deduplicated;
    }

    fn installable_expression(
        &self,
        smt: &dyn crate::problem_context::ProblemContext,
        expression: &ArrayExpr,
    ) -> Option<Term> {
        let term_hash = crate::training::canonical_term_hash(expression);
        let term = expr_to_term(expression.clone());
        if self.aux_covered_term_hashes.contains(&term_hash)
            || term_contains_auxiliary_symbol(&term)
        {
            return None;
        }
        smt.make_unquantified_instance(term)
            .map(|instance| canonical_instantiation_key(instance.get_term()))
    }

    fn absorb_candidates(
        &mut self,
        state: &mut ArrayRefinementState,
        smt: &dyn crate::problem_context::ProblemContext,
        batch: InstantiationBatch,
        refinement_step: u32,
    ) -> CandidateSummary {
        let selected_candidates = batch.selected().count();
        let conflicts_count = batch
            .selected()
            .filter(|candidate| candidate.conflict.is_some())
            .count();
        let summary = CandidateSummary {
            selected_candidates,
            conflicts: conflicts_count,
        };
        let selection_history = batch
            .candidates
            .iter()
            .flat_map(|candidate| candidate.selection_history.iter())
            .cloned()
            .collect::<Vec<_>>();
        for selection in &selection_history {
            self.term_selection_decisions.insert(
                selection.decision_key.clone(),
                selection.chosen_term_hash.clone(),
            );
        }
        for selection in selection_history {
            if let Some(term_hash) = self.term_selection_decisions.get(&selection.decision_key) {
                *self
                    .term_selection_counts
                    .entry(term_hash.clone())
                    .or_default() += 1;
            }
        }
        let mut conflicts = Vec::with_capacity(conflicts_count);
        for mut candidate in batch.candidates {
            for decision in mem::take(&mut candidate.decisions) {
                if !self
                    .decision_data
                    .iter()
                    .any(|known| known.decision_key == decision.decision_key)
                {
                    self.decision_data.push(decision);
                }
            }
            if let Some(mut record) = candidate.abstract_instantiation.take() {
                record.was_selected = candidate.selected;
                if let Some(known) = self.abstract_instantiations.iter_mut().find(|known| {
                    known.abstract_instantiation_id == record.abstract_instantiation_id
                }) {
                    known.was_selected |= record.was_selected;
                    for decision_key in record.decision_keys {
                        if !known.decision_keys.contains(&decision_key) {
                            known.decision_keys.push(decision_key);
                        }
                    }
                } else {
                    self.abstract_instantiations.push(record);
                }
            }

            if !candidate.selected {
                continue;
            }
            if let Some(conflict) = candidate.conflict.take() {
                conflicts.push(conflict);
            }

            state.candidates.push(candidate);
        }
        self.handle_aux_synthesis_detection(state, smt, &conflicts, refinement_step);
        summary
    }

    fn finish_profiling_record(&mut self, profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>) {
        if let Some(profiling) = profiling {
            if let Ok(profiling) = Rc::try_unwrap(profiling) {
                self.profiling_records.push(profiling.into_inner().finish());
            } else {
                warn!("Unable to unwrap array profiling collector; profiling record dropped");
            }
        }
    }

    fn handle_aux_synthesis_detection(
        &mut self,
        state: &ArrayRefinementState,
        smt: &dyn crate::problem_context::ProblemContext,
        conflicts: &[ArrayConflictRecord],
        refinement_step: u32,
    ) {
        if self.aux_config.is_off() {
            return;
        }
        let eligible_conflicts = conflicts
            .iter()
            .filter(|conflict| !term_contains_auxiliary_symbol(&conflict.term))
            .cloned()
            .collect::<Vec<_>>();
        let ignored_aux_conflicts = conflicts.len().saturating_sub(eligible_conflicts.len());
        if ignored_aux_conflicts > 0 {
            info!(
                "AUX-SYNTH ignored {ignored_aux_conflicts} conflicts containing auxiliary symbols"
            );
        }
        let decision = self.aux_trigger_state.decide(
            &self.aux_config,
            &eligible_conflicts,
            refinement_step,
            250,
        );
        if decision.detected_conflicts.is_empty()
            && self.aux_config.trigger == SynthesisTrigger::Detect
        {
            info!(
                "AUX-SYNTH detect depth={} refinement_step={}: no non-local conflicts",
                state.depth, refinement_step
            );
            return;
        }
        info!(
            "AUX-SYNTH trigger={} guard={} depth={} refinement_step={} fired={} reason={} detected={}",
            self.aux_config.trigger,
            self.aux_config.guard_policy,
            state.depth,
            refinement_step,
            decision.fired,
            decision.reason,
            decision.detected_conflicts.len()
        );
        for conflict_id in &decision.detected_conflicts {
            if let Some(conflict) = eligible_conflicts
                .iter()
                .find(|conflict| conflict.conflict_id == *conflict_id)
            {
                info!(
                    "AUX-SYNTH detected conflict={} axiom={} span={} frames={:?} cost={} term={}",
                    conflict.conflict_id,
                    conflict.axiom_name,
                    conflict.frame_span.span,
                    conflict.frame_span.frames,
                    conflict.cost,
                    conflict.term
                );
            }
        }
        if !decision.fired {
            return;
        }
        let Some(selected_conflict_id) = decision.selected_conflict_id else {
            return;
        };
        if self.installed_aux_conflicts.contains(&selected_conflict_id) {
            return;
        }
        let Some(conflict) = eligible_conflicts
            .iter()
            .find(|conflict| conflict.conflict_id == selected_conflict_id)
        else {
            warn!("AUX-SYNTH selected conflict {selected_conflict_id} was not found");
            return;
        };
        if self.aux_config.guard_policy != crate::auxiliary_synthesis::GuardPolicy::True {
            warn!(
                "AUX-SYNTH guard policy {} is not implemented for installation yet; using true",
                self.aux_config.guard_policy
            );
        }
        match AuxiliarySpec::from_conflict(
            conflict,
            smt.get_variables(),
            self.aux_config.trigger,
            self.aux_config.guard_policy,
        ) {
            Ok(spec) => {
                info!(
                    "AUX-SYNTH queued aux_id={} source_conflict={} history={} prophecy={:?}",
                    spec.aux_id,
                    spec.source_conflict_id,
                    spec.history.name,
                    spec.prophecy.as_ref().map(|prophecy| prophecy.name.clone())
                );
                self.installed_aux_conflicts.insert(selected_conflict_id);
                self.aux_covered_term_hashes
                    .insert(spec.source_term_hash.clone());
                self.pending_aux_specs.push(spec);
            }
            Err(err) => warn!(
                "AUX-SYNTH could not build auxiliary spec for conflict {}: {err}",
                conflict.conflict_id
            ),
        }
    }
}
