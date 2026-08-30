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
    instantiation_strategy::assertion_tracker::canonical_instantiation_key,
    profiling::{ArrayProfilingCollector, ProfilingRecord, ProfilingRunRecord},
    quantified_rule::TransitionGuardRule,
    solver::PropertyCheckMode,
    theories::array::{
        array_axioms::{
            expr_to_term, generate_array_instantiation_candidates, ArrayExpr,
            ArrayInstantiationInstrumentation, ArrayInstantiationOptions, ArrayLanguage,
        },
        array_dataflow::{build_property_cone, PropertyCone},
        array_egraph_builder::{
            ArrayEGraphBuildStage, ArrayEGraphBuildStep, ArrayEGraphBuilder, FullEGraphBuilder,
            SourceThenFullEGraphBuilder,
        },
        array_rule_instantiator::ArrayArtifactCapture,
        array_term_extractor::{ArrayTermExtractor, ArrayTermExtractorOptions},
        instantiation_candidate::{InstantiationBatch, InstantiationCandidate},
        instantiation_ranker::{InstantiationRanker, PreferSourceInstantiationRanker},
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
    candidate_winners_per_group: usize,
    instantiation_ranker: Box<dyn InstantiationRanker>,
    property_check_mode: PropertyCheckMode,
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
            egraph_builder: Box::<SourceThenFullEGraphBuilder>::default(),
            cone_attempted_depths: HashSet::new(),
            property_cone: PropertyCone::default(),
            preprocess_exact_read_after_write: false,
            candidate_winners_per_group: 1,
            instantiation_ranker: Box::new(PreferSourceInstantiationRanker),
            property_check_mode: PropertyCheckMode::Scoped,
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

    pub fn with_candidate_winners_per_group(mut self, winners_per_group: usize) -> Self {
        assert!(winners_per_group > 0, "candidate groups need a winner");
        self.candidate_winners_per_group = winners_per_group;
        self
    }

    pub fn with_instantiation_ranker(
        mut self,
        instantiation_ranker: Box<dyn InstantiationRanker>,
    ) -> Self {
        self.instantiation_ranker = instantiation_ranker;
        self
    }

    pub fn with_property_check_mode(mut self, mode: PropertyCheckMode) -> Self {
        self.property_check_mode = mode;
        self
    }
}

fn egraph_node_count<N>(egraph: &egg::EGraph<ArrayLanguage, N>) -> usize
where
    N: egg::Analysis<ArrayLanguage>,
{
    egraph.classes().map(|class| class.nodes.len()).sum()
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

    fn property_check_mode(&self) -> PropertyCheckMode {
        self.property_check_mode
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

    fn has_pending_refinement(&self, state: &ArrayRefinementState) -> bool {
        !state.candidates.is_empty() || !self.pending_aux_specs.is_empty()
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
        // The driver may call `sat` again with this same state after concrete
        // validation rejects the current abstract counterexample.
        #[allow(clippy::never_loop)]
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
                    return Err(driver::Error::AbstractionExhausted { depth: state.depth });
                }
            };
            if let Some(profiling) = &profiling {
                let mut profiling = profiling.borrow_mut();
                profiling.record_timing("egraph_build", build_start.elapsed());
                profiling.add_counter("egraph_build_stages", 1);
                profiling.add_counter(
                    match expansion.stage {
                        ArrayEGraphBuildStage::Source => "egraph_build_source_stages",
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
            let candidate_catalog = if expansion.candidate_scope.tracks_provenance()
                || self.instantiation_ranker.requires_source_provenance()
            {
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
            let mut pruned_guards = Vec::new();
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
                    let generation = generate_guard_candidates(
                        rule,
                        &state.egraph,
                        &guard_extractor,
                        cost_fn.clone(),
                        state.depth,
                        smt,
                    )?;
                    pruned_guards.push((
                        rule.metadata().name().to_string(),
                        generation.rejected_by_model,
                    ));
                    candidate_batch.extend(generation.candidates);
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
            let mut summary = candidate_batch.prepare_with_ranker(
                expansion.candidate_scope,
                &known_instantiations,
                self.candidate_winners_per_group,
                self.instantiation_ranker.as_ref(),
                |term| smt.eval_to_string(term),
                |candidate| self.installable_expression(smt, &candidate.expression),
            )?;
            for (rule_name, count) in pruned_guards {
                summary.record_pruned_model_candidates(&rule_name, count);
            }

            if let Some(profiling) = &profiling {
                let mut profiling = profiling.borrow_mut();
                for (rule_name, counts) in &summary.by_rule {
                    profiling.record_rule_candidates(rule_name, counts.generated, counts.selected);
                }
                profiling.add_counter(
                    "model_satisfied_instantiations_filtered",
                    summary.rejected_model as u64,
                );
                profiling.add_counter(
                    "duplicate_or_uninstallable_instantiations_filtered",
                    summary.rejected_known as u64,
                );
                profiling.add_counter(
                    "instantiation_ranker_candidates_filtered",
                    summary.rejected_ranker as u64,
                );
            }

            self.absorb_candidates(state, smt, candidate_batch, refinement_step);

            if let Some(profiling) = &profiling {
                profiling
                    .borrow_mut()
                    .record_timing("instantiation_total", instantiation_start.elapsed());
            }

            if trace_conflicts_enabled() {
                trace!(
                    "[yardbird::conflict-trace] sat depth={} refinement_step={} build_stage={} selected_guards={} selected_arrays={} conflicts={}",
                    state.depth,
                    refinement_step,
                    expansion.stage.as_str(),
                    summary.selected_guards,
                    summary.selected_arrays,
                    summary.conflicts,
                );
            }
            if summary.selected_count() > 0 {
                self.finish_profiling_record(profiling);
                return Ok(ProofAction::Continue);
            }

            self.finish_profiling_record(profiling);
            return Ok(ProofAction::Continue);
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
    ) {
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
        let mut conflicts = Vec::new();
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
            if let Some(record) = candidate.abstract_instantiation.take() {
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
