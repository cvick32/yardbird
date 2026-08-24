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
    quantified_rule::TransitionGuardRule,
    theories::array::{
        array_axioms::{
            expr_to_term, saturate_with_array_types, ArrayAxiomInstantiation, ArrayExpr,
            ArrayLanguage, ArraySaturationInstrumentation, ArraySaturationOptions,
            ArraySaturationResult,
        },
        array_conflict_scheduler::ArrayArtifactCapture,
        array_dataflow::{build_property_cone, PropertyCone},
        array_egraph_builder::{
            ArrayEGraphBuildStage, ArrayEGraphBuildStep, ArrayEGraphBuilder, FullEGraphBuilder,
        },
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
            const_instantiations: vec![],
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
    fn reversed_equalities_are_duplicate_before_whole_candidate_selection() {
        let installed: ArrayExpr = "(= (Read Int Int a@0 i@0) 0)".parse().unwrap();
        let reversed: ArrayExpr = "(= 0 (Read Int Int a@0 i@0))".parse().unwrap();
        let mut candidates = vec![reversed];
        let installed =
            UnquantifiedInstantiator::rewrite_unquantified(expr_to_term(installed), vec![])
                .unwrap();
        let mut known = HashSet::from([canonical_instantiation_key(installed.get_term())]);

        let duplicates = retain_novel_by(&mut candidates, &mut known, |expression| {
            UnquantifiedInstantiator::rewrite_unquantified(expr_to_term(expression.clone()), vec![])
                .map(|instance| canonical_instantiation_key(instance.get_term()))
        });

        assert_eq!(duplicates.len(), 1);
        assert!(candidates.is_empty());
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
    pub instantiations: Vec<ArrayAxiomInstantiation>,
    pub const_instantiations: Vec<ArrayAxiomInstantiation>,
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
        self.transition_guard_rules = abstracted_model
            .get_transition_guards()
            .into_iter()
            .enumerate()
            .map(|(ordinal, guard)| TransitionGuardRule::from_parsed(guard, ordinal))
            .collect();
        if !self.transition_guard_rules.is_empty() {
            info!(
                "Discovered {} quantified transition guard(s)",
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
            instantiations: vec![],
            const_instantiations: vec![],
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

            let saturation_start = Instant::now();
            let mut known_instantiations = smt
                .get_instantiations()
                .into_iter()
                .map(|term| canonical_instantiation_key(&term))
                .collect::<HashSet<_>>();
            let mut excluded_instantiations = HashSet::new();
            let require_model_violation = expansion.candidate_scope.requires_model_violation();
            let retry_rejected_candidates =
                expansion.candidate_scope.retries_rejected_instantiations();
            let summary = loop {
                let mut saturation = saturate_with_array_types(
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
                    |expr| self.installable_instance(smt, expr),
                );
                let rejected_const = retain_novel_by(
                    &mut saturation.const_instantiations,
                    &mut known_instantiations,
                    |expr| self.installable_instance(smt, expr),
                );
                let installable_candidate_ids = saturation
                    .instantiations
                    .iter()
                    .chain(&saturation.const_instantiations)
                    .map(|candidate| candidate.provenance.abstract_instantiation_id())
                    .collect::<HashSet<_>>();
                for record in &mut saturation.abstract_instantiations {
                    record.was_selected = installable_candidate_ids
                        .contains(record.abstract_instantiation_id.as_str());
                }
                let rejected_model_count =
                    rejected_model_regular.len() + rejected_model_const.len();
                let rejected_count =
                    rejected_model_count + rejected_regular.len() + rejected_const.len();
                excluded_instantiations.extend(
                    rejected_model_regular
                        .into_iter()
                        .map(|candidate| candidate.expression),
                );
                excluded_instantiations.extend(
                    rejected_model_const
                        .into_iter()
                        .map(|candidate| candidate.expression),
                );
                excluded_instantiations.extend(
                    rejected_regular
                        .into_iter()
                        .map(|candidate| candidate.expression),
                );
                excluded_instantiations.extend(
                    rejected_const
                        .into_iter()
                        .map(|candidate| candidate.expression),
                );
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
        for (kind, candidate) in state
            .const_instantiations
            .into_iter()
            .map(|candidate| ("const", candidate))
            .chain(
                state
                    .instantiations
                    .into_iter()
                    .map(|candidate| ("regular", candidate)),
            )
        {
            let term_hash = crate::training::canonical_term_hash(&candidate.expression);
            let term = expr_to_term(candidate.expression.clone());
            if self.aux_covered_term_hashes.contains(&term_hash) {
                info!("AUX-SYNTH skipped aux-covered {kind} instantiation");
                continue;
            }
            if term_contains_auxiliary_symbol(&term) {
                info!("AUX-SYNTH skipped {kind} instantiation containing auxiliary symbols");
                continue;
            }

            let abstract_id = candidate.provenance.abstract_instantiation_id().to_string();
            if trace_instantiations {
                trace!(
                    "[yardbird::inst-trace] {kind} abstract-hash={term_hash} abstract-id={abstract_id} abstract-term={term} substitution={:?}",
                    candidate.provenance.relative_substitution(),
                );
            }
            if kind == "const" {
                self.const_instantiations.push(term.clone());
            }

            let Some(request) =
                smt.make_provenanced_unquantified_instance(term, candidate.provenance)
            else {
                if trace_instantiations {
                    trace!("[yardbird::inst-trace] {kind} rewrite-none abstract-id={abstract_id}");
                }
                continue;
            };
            let result = smt.add_instantiation(request);
            self.record_installation_outcome(&abstract_id, result);
            if trace_instantiations {
                trace!(
                    "[yardbird::inst-trace] {kind} add-result abstract-id={abstract_id} abstract-added={} solver-assertions-added={} indexed-deduplicated={} helper-deduplicated={}",
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

fn retain_novel_by<T, K>(
    instantiations: &mut Vec<T>,
    known: &mut HashSet<K>,
    mut normalize: impl FnMut(&T) -> Option<K>,
) -> Vec<T>
where
    T: Clone,
    K: Eq + Hash,
{
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

trait HasArrayExpression {
    fn array_expression(&self) -> &ArrayExpr;
}

impl HasArrayExpression for ArrayExpr {
    fn array_expression(&self) -> &ArrayExpr {
        self
    }
}

impl HasArrayExpression for ArrayAxiomInstantiation {
    fn array_expression(&self) -> &ArrayExpr {
        &self.expression
    }
}

fn retain_model_violations<T>(
    instantiations: &mut Vec<T>,
    mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
) -> anyhow::Result<Vec<T>>
where
    T: Clone + HasArrayExpression,
{
    let mut rejected = Vec::new();
    let mut evaluation_error = None;
    instantiations.retain(|instantiation| {
        let term = expr_to_term(instantiation.array_expression().clone());
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

    fn installable_instance(
        &self,
        smt: &dyn crate::problem_context::ProblemContext,
        instantiation: &ArrayAxiomInstantiation,
    ) -> Option<Term> {
        let term_hash = crate::training::canonical_term_hash(&instantiation.expression);
        let term = expr_to_term(instantiation.expression.clone());
        if self.aux_covered_term_hashes.contains(&term_hash)
            || term_contains_auxiliary_symbol(&term)
        {
            return None;
        }
        smt.make_unquantified_instance(term)
            .map(|instance| canonical_instantiation_key(instance.get_term()))
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
        for decision in saturation.decisions {
            if !self
                .decision_data
                .iter()
                .any(|known| known.decision_key == decision.decision_key)
            {
                self.decision_data.push(decision);
            }
        }
        for record in saturation.abstract_instantiations {
            if let Some(known) = self
                .abstract_instantiations
                .iter_mut()
                .find(|known| known.abstract_instantiation_id == record.abstract_instantiation_id)
            {
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
