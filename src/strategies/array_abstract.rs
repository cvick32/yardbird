use std::{cell::RefCell, collections::HashSet, mem, rc::Rc, time::Instant};

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
    profiling::{ArrayProfilingCollector, ProfilingRecord, ProfilingRunRecord},
    theories::array::{
        array_axioms::{
            expr_to_term, saturate_with_array_types_and_ranker, ArrayExpr, ArrayLanguage,
            ArraySaturationInstrumentation, ArraySaturationOptions, ArraySaturationResult,
        },
        array_conflict_scheduler::ArrayArtifactCapture,
        array_dataflow::{build_property_cone, PropertyCone},
        array_egraph_builder::{
            ArrayEGraphBuildStage, ArrayEGraphBuildStep, ArrayEGraphBuilder, FullEGraphBuilder,
        },
        array_instantiation_ranker::{ArrayInstantiationRanker, CompleteCostInstantiationRanker},
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
    const_instantiations: Vec<Term>,
    _bmc_depth: u16,
    run_ic3ia: bool,
    cost_config: F::Config,
    discovered_array_types: Vec<(String, String)>,
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
    instantiation_ranker: Box<dyn ArrayInstantiationRanker>,
    property_cone: PropertyCone,
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
            const_instantiations: vec![],
            cost_config,
            discovered_array_types: vec![],
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
            instantiation_ranker: Box::<CompleteCostInstantiationRanker>::default(),
            property_cone: PropertyCone::default(),
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

    pub fn with_instantiation_ranker(
        mut self,
        instantiation_ranker: Box<dyn ArrayInstantiationRanker>,
    ) -> Self {
        self.instantiation_ranker = instantiation_ranker;
        self
    }
}

#[cfg(test)]
mod tests {
    use smt2parser::vmt::quantified_instantiator::UnquantifiedInstantiator;

    use super::*;

    #[test]
    fn shifted_copies_of_an_instantiation_are_duplicate_after_normalization() {
        let installed = "(=> (not (= i@12 i@11)) (= (Read Int Int a@11 i@12) 0))"
            .parse::<ArrayExpr>()
            .unwrap();
        let mut instantiations = vec!["(=> (not (= i@5 i@4)) (= (Read Int Int a@4 i@5) 0))"
            .parse::<ArrayExpr>()
            .unwrap()];
        let mut known = HashSet::from([UnquantifiedInstantiator::rewrite_unquantified(
            expr_to_term(installed),
            vec![],
        )
        .unwrap()
        .get_term()
        .clone()]);

        let duplicates = retain_novel_by(&mut instantiations, &mut known, |expr| {
            UnquantifiedInstantiator::rewrite_unquantified(expr_to_term(expr.clone()), vec![])
                .map(|instance| instance.get_term().clone())
        });

        assert_eq!(duplicates.len(), 1);
        assert!(instantiations.is_empty());
        assert_eq!(known.len(), 1);
    }

    #[test]
    fn only_axioms_false_in_the_current_model_remain_eligible() {
        let satisfied: ArrayExpr = "(= (Read Int Int A i) v)".parse().unwrap();
        let violated: ArrayExpr = "(= (Read Int Int B j) w)".parse().unwrap();
        let mut candidates = vec![satisfied.clone(), violated.clone()];

        let rejected = retain_model_violations(&mut candidates, |term| {
            Ok(if term.to_string().contains("Read_Int_Int A") {
                "true".to_string()
            } else {
                "false".to_string()
            })
        })
        .unwrap();

        assert_eq!(candidates, vec![violated]);
        assert_eq!(rejected, vec![satisfied]);
    }
}

fn egraph_node_count<N>(egraph: &egg::EGraph<ArrayLanguage, N>) -> usize
where
    N: egg::Analysis<ArrayLanguage>,
{
    egraph.classes().map(|class| class.nodes.len()).sum()
}

#[derive(Clone, Copy, Debug)]
struct SaturationSummary {
    regular_instantiations: usize,
    const_instantiations: usize,
    conflicts: usize,
}

/// State for the inner refinement looop
pub struct ArrayRefinementState {
    pub depth: u16,
    pub egraph: egg::EGraph<ArrayLanguage, ()>,
    pub instantiations: Vec<ArrayExpr>,
    pub const_instantiations: Vec<ArrayExpr>,
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
        let (abstracted_model, discovered_types) = model.abstract_array_theory();
        self.property_cone = if self.egraph_builder.requires_property_cone() {
            build_property_cone(&abstracted_model)
        } else {
            PropertyCone::default()
        };
        self.discovered_array_types = discovered_types;
        abstracted_model
        //     .abstract_constants_over(self.bmc_depth)
    }

    fn setup(
        &mut self,
        smt: &dyn crate::problem_context::ProblemContext,
        depth: u16,
    ) -> driver::Result<ArrayRefinementState> {
        let egraph = egg::EGraph::new(());
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
            instantiations: vec![],
            const_instantiations: vec![],
            array_types,
            egraph_builder: self.egraph_builder.clone(),
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

            let saturation_start = Instant::now();
            let mut known_instantiations =
                smt.get_instantiations().into_iter().collect::<HashSet<_>>();
            let mut excluded_instantiations = HashSet::new();
            let require_model_violation = expansion.candidate_scope.requires_model_violation();
            let retry_rejected_candidates =
                expansion.candidate_scope.retries_rejected_instantiations();
            let summary = loop {
                let mut saturation = saturate_with_array_types_and_ranker(
                    &mut state.egraph,
                    cost_fn.clone(),
                    &state.array_types,
                    ArraySaturationOptions {
                        candidate_catalog: candidate_catalog.clone(),
                        candidate_scope: expansion.candidate_scope,
                        excluded_instantiations: excluded_instantiations.clone(),
                        refinement_step,
                        selection_counts: self.term_selection_counts.clone(),
                        depth: state.depth,
                        instrumentation: ArraySaturationInstrumentation {
                            artifact_capture: self.artifact_capture,
                            profiling: profiling.clone(),
                        },
                    },
                    self.instantiation_ranker.as_ref(),
                );
                let (rejected_model_regular, rejected_model_const) = if require_model_violation {
                    (
                        retain_model_violations(&mut saturation.instantiations, |term| {
                            smt.eval_to_string(term)
                        })?,
                        retain_model_violations(&mut saturation.const_instantiations, |term| {
                            smt.eval_to_string(term)
                        })?,
                    )
                } else {
                    (Vec::new(), Vec::new())
                };
                let rejected_regular = retain_novel_by(
                    &mut saturation.instantiations,
                    &mut known_instantiations,
                    |expr| self.installable_instance_term(smt, expr),
                );
                let rejected_const = retain_novel_by(
                    &mut saturation.const_instantiations,
                    &mut known_instantiations,
                    |expr| self.installable_instance_term(smt, expr),
                );
                let rejected_model_count =
                    rejected_model_regular.len() + rejected_model_const.len();
                let rejected_count =
                    rejected_model_count + rejected_regular.len() + rejected_const.len();
                excluded_instantiations.extend(rejected_model_regular);
                excluded_instantiations.extend(rejected_model_const);
                excluded_instantiations.extend(rejected_regular);
                excluded_instantiations.extend(rejected_const);
                if let Some(profiling) = &profiling {
                    let mut profiling = profiling.borrow_mut();
                    profiling.add_counter(
                        "model_satisfied_instantiations_filtered",
                        rejected_model_count as u64,
                    );
                    profiling.add_counter(
                        "duplicate_or_uninstallable_instantiations_filtered",
                        (rejected_count - rejected_model_count) as u64,
                    );
                }

                let summary = self.absorb_saturation(state, smt, saturation, refinement_step);
                if summary.regular_instantiations > 0
                    || summary.const_instantiations > 0
                    || rejected_count == 0
                    || !retry_rejected_candidates
                {
                    break summary;
                }
            };
            if let Some(profiling) = &profiling {
                profiling
                    .borrow_mut()
                    .record_timing("saturation_total", saturation_start.elapsed());
            }

            if trace_conflicts_enabled() {
                trace!(
                    "[yardbird::conflict-trace] sat depth={} refinement_step={} build_stage={} produced regular_insts={} const_insts={} conflicts={} total_regular={} total_const={}",
                    state.depth,
                    refinement_step,
                    expansion.stage.as_str(),
                    summary.regular_instantiations,
                    summary.const_instantiations,
                    summary.conflicts,
                    state.instantiations.len(),
                    state.const_instantiations.len()
                );
            }
            if summary.regular_instantiations > 0 || summary.const_instantiations > 0 {
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
        let raw_const_pairs: Vec<(String, Term)> = state
            .const_instantiations
            .iter()
            .map(|inst| {
                (
                    crate::training::canonical_term_hash(inst),
                    expr_to_term(inst.clone()),
                )
            })
            .collect();
        let skipped_const_aux_symbol = raw_const_pairs
            .iter()
            .filter(|(_, term)| term_contains_auxiliary_symbol(term))
            .count();
        let const_pairs: Vec<(String, Term)> = raw_const_pairs
            .into_iter()
            .filter(|(term_hash, _)| !self.aux_covered_term_hashes.contains(term_hash))
            .filter(|(_, term)| !term_contains_auxiliary_symbol(term))
            .collect();
        let skipped_const_aux_covered = state
            .const_instantiations
            .iter()
            .filter(|inst| {
                self.aux_covered_term_hashes
                    .contains(&crate::training::canonical_term_hash(inst))
            })
            .count();
        if skipped_const_aux_covered > 0 {
            info!("AUX-SYNTH skipped {skipped_const_aux_covered} aux-covered const instantiations");
        }
        if skipped_const_aux_symbol > 0 {
            info!(
                "AUX-SYNTH skipped {skipped_const_aux_symbol} const instantiations containing auxiliary symbols"
            );
        }
        for (term_hash, term) in &const_pairs {
            if trace_instantiations {
                trace!(
                    "[yardbird::inst-trace] const abstract-hash={} abstract-term={}",
                    term_hash,
                    term
                );
            }
            if let Some(inst) = smt.make_unquantified_instance(term.clone()) {
                let abstract_id = self
                    .abstract_instantiations
                    .iter()
                    .find(|record| record.term_hash == *term_hash)
                    .map(|record| record.abstract_instantiation_id.clone());
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] const concrete abstract-hash={} abstract-id={abstract_id:?} concrete-term={}",
                        term_hash,
                        inst
                    );
                }
                let added = smt.add_instantiation(inst, abstract_id);
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] const add-result abstract-hash={} added={added}",
                        term_hash
                    );
                }
            } else if trace_instantiations {
                trace!(
                    "[yardbird::inst-trace] const rewrite-none abstract-hash={}",
                    term_hash
                );
            }
        }
        self.const_instantiations
            .extend(const_pairs.iter().map(|(_, term)| term.clone()));

        let raw_terms: Vec<(String, Term)> = state
            .instantiations
            .iter()
            .map(|inst| {
                let hash = crate::training::canonical_term_hash(inst);
                (hash, expr_to_term(inst.clone()))
            })
            .collect();
        let skipped_regular_aux_symbol = raw_terms
            .iter()
            .filter(|(_, term)| term_contains_auxiliary_symbol(term))
            .count();
        let terms: Vec<(String, Term)> = raw_terms
            .into_iter()
            .filter(|(term_hash, _)| !self.aux_covered_term_hashes.contains(term_hash))
            .filter(|(_, term)| !term_contains_auxiliary_symbol(term))
            .collect();
        let skipped_regular_aux_covered = state
            .instantiations
            .iter()
            .filter(|inst| {
                self.aux_covered_term_hashes
                    .contains(&crate::training::canonical_term_hash(inst))
            })
            .count();
        if skipped_regular_aux_covered > 0 {
            info!(
                "AUX-SYNTH skipped {skipped_regular_aux_covered} aux-covered regular instantiations"
            );
        }
        if skipped_regular_aux_symbol > 0 {
            info!(
                "AUX-SYNTH skipped {skipped_regular_aux_symbol} regular instantiations containing auxiliary symbols"
            );
        }
        let instances = terms
            .into_iter()
            .filter_map(|(term_hash, term)| {
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] regular abstract-hash={} abstract-term={}",
                        term_hash,
                        term
                    );
                }
                smt.make_unquantified_instance(term)
                    .map(move |inst| (term_hash.clone(), inst))
            })
            .collect::<Vec<_>>();
        let _ = instances
            .into_iter()
            .map(|(term_hash, inst)| {
                let abstract_id = self
                    .abstract_instantiations
                    .iter()
                    .find(|record| record.term_hash == term_hash)
                    .map(|record| record.abstract_instantiation_id.clone());
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] regular concrete abstract-hash={} abstract-id={abstract_id:?} concrete-term={}",
                        term_hash,
                        inst
                    );
                }
                let added = smt.add_instantiation(inst, abstract_id);
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] regular add-result abstract-hash={} added={added}",
                        term_hash
                    );
                }
                !added
            })
            .fold(true, |a, b| a && b);

        if !self.pending_aux_specs.is_empty() {
            let specs = mem::take(&mut self.pending_aux_specs);
            info!("AUX-SYNTH installing {} auxiliary specs", specs.len());
            smt.install_auxiliary_specs(specs)?;
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
            const_instances: mem::take(&mut self.const_instantiations),
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

fn retain_novel_by(
    instantiations: &mut Vec<ArrayExpr>,
    known: &mut HashSet<Term>,
    mut normalize: impl FnMut(&ArrayExpr) -> Option<Term>,
) -> Vec<ArrayExpr> {
    let mut rejected = Vec::new();
    instantiations.retain(|instantiation| {
        let keep = normalize(instantiation).is_some_and(|normalized| known.insert(normalized));
        if !keep {
            rejected.push(instantiation.clone());
        }
        keep
    });
    rejected
}

fn retain_model_violations(
    instantiations: &mut Vec<ArrayExpr>,
    mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
) -> anyhow::Result<Vec<ArrayExpr>> {
    let mut rejected = Vec::new();
    let mut evaluation_error = None;
    instantiations.retain(|instantiation| {
        let term = expr_to_term(instantiation.clone());
        match evaluate(&term) {
            Ok(value) if value.trim() == "false" => true,
            Ok(_) => {
                rejected.push(instantiation.clone());
                false
            }
            Err(error) => {
                evaluation_error = Some(error);
                false
            }
        }
    });
    if let Some(error) = evaluation_error {
        return Err(error);
    }
    Ok(rejected)
}

impl<F> Abstract<F>
where
    F: ArrayCostFactory + 'static,
{
    fn installable_instance_term(
        &self,
        smt: &dyn crate::problem_context::ProblemContext,
        instantiation: &ArrayExpr,
    ) -> Option<Term> {
        let term_hash = crate::training::canonical_term_hash(instantiation);
        let term = expr_to_term(instantiation.clone());
        if self.aux_covered_term_hashes.contains(&term_hash)
            || term_contains_auxiliary_symbol(&term)
        {
            return None;
        }
        smt.make_unquantified_instance(term)
            .map(|instance| instance.get_term().clone())
    }

    fn absorb_saturation(
        &mut self,
        state: &mut ArrayRefinementState,
        smt: &dyn crate::problem_context::ProblemContext,
        saturation: ArraySaturationResult,
        refinement_step: u32,
    ) -> SaturationSummary {
        let summary = SaturationSummary {
            regular_instantiations: saturation.instantiations.len(),
            const_instantiations: saturation.const_instantiations.len(),
            conflicts: saturation.conflicts.len(),
        };
        state.instantiations.extend(saturation.instantiations);
        state
            .const_instantiations
            .extend(saturation.const_instantiations);
        self.decision_data.extend(saturation.decisions);
        self.abstract_instantiations
            .extend(saturation.abstract_instantiations);
        for (decision_key, term_hash) in saturation.selection_history_decisions {
            self.term_selection_decisions
                .insert(decision_key, term_hash);
        }
        for decision_keys in saturation.instantiation_decision_keys {
            for decision_key in decision_keys {
                if let Some(term_hash) = self.term_selection_decisions.get(&decision_key) {
                    *self
                        .term_selection_counts
                        .entry(term_hash.clone())
                        .or_default() += 1;
                }
            }
        }
        self.handle_aux_synthesis_detection(state, smt, &saturation.conflicts, refinement_step);
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
                    "AUX-SYNTH detected conflict={} axiom={} span={} frames={:?} cost={} class={:?} term={}",
                    conflict.conflict_id,
                    conflict.axiom_name,
                    conflict.frame_span.span,
                    conflict.frame_span.frames,
                    conflict.cost,
                    conflict.classification,
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
