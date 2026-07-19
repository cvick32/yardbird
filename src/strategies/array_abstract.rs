use std::{cell::RefCell, collections::HashSet, mem, rc::Rc, time::Instant};

use log::{info, trace, warn};
use rustc_hash::FxHashMap;
use smt2parser::{
    concrete::Term,
    vmt::{quantified_instantiator::UnquantifiedInstantiator, VMTModel},
};

use crate::{
    auxiliary_synthesis::{
        term_contains_auxiliary_symbol, ArrayConflictRecord, AuxSynthesisConfig, AuxTriggerState,
        AuxiliarySpec, SynthesisTrigger,
    },
    cost_functions::array::ArrayCostFactory,
    driver::{self},
    ic3ia::{call_ic3ia, ic3ia_output_contains_proof},
    profiling::{ArrayProfilingCollector, ProfilingRecord, ProfilingRunRecord},
    theories::array::{
        array_axioms::{
            expr_to_term, saturate_with_array_types, translate_term, ArrayExpr, ArrayLanguage,
            ArraySaturationInstrumentation,
        },
        array_conflict_scheduler::{preprocess_array_expr, ArrayArtifactCapture},
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
    profile_costs: bool,
    profiling_records: Vec<ProfilingRecord>,
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
        profile_costs: bool,
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
            profile_costs,
            profiling_records: vec![],
        }
    }

    pub fn with_artifact_capture(mut self, mut artifact_capture: ArrayArtifactCapture) -> Self {
        artifact_capture.conflicts |= !self.aux_config.is_off();
        self.artifact_capture = artifact_capture;
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
    pub instantiations: Vec<ArrayExpr>,
    pub const_instantiations: Vec<ArrayExpr>,
    pub array_types: Vec<(String, String)>,
}

impl ArrayRefinementState {
    pub fn update_with_subterms(
        &mut self,
        smt: &dyn crate::problem_context::ProblemContext,
        profiling: Option<&Rc<RefCell<ArrayProfilingCollector>>>,
    ) -> anyhow::Result<()> {
        let all_subterms_start = Instant::now();
        let subterms = smt.get_all_subterms();
        if let Some(profiling) = profiling {
            let mut profiling = profiling.borrow_mut();
            profiling.record_timing("update_get_all_subterms", all_subterms_start.elapsed());
            profiling.add_counter("update_subterms", subterms.len() as u64);
        }

        for term in subterms {
            let eval_start = Instant::now();
            let interp_str = smt.eval_to_string(term)?;
            if let Some(profiling) = profiling {
                profiling
                    .borrow_mut()
                    .record_timing("update_eval_to_string", eval_start.elapsed());
            }

            let translate_start = Instant::now();
            let translated = translate_term(term.clone()).unwrap();
            if let Some(profiling) = profiling {
                profiling
                    .borrow_mut()
                    .record_timing("update_translate_term", translate_start.elapsed());
            }

            let parse_start = Instant::now();
            let preprocessed = preprocess_array_expr(&interp_str);
            let parsed_interp = preprocessed.parse()?;
            if let Some(profiling) = profiling {
                profiling
                    .borrow_mut()
                    .record_timing("update_preprocess_parse_interp", parse_start.elapsed());
            }

            let egraph_start = Instant::now();
            let term_id = self.egraph.add_expr(&translated);
            let interp_id = self.egraph.add_expr(&parsed_interp);
            self.egraph.union(term_id, interp_id);
            if let Some(profiling) = profiling {
                profiling
                    .borrow_mut()
                    .record_timing("update_egraph_add_union", egraph_start.elapsed());
            }
        }

        let rebuild_start = Instant::now();
        self.egraph.rebuild();
        if let Some(profiling) = profiling {
            profiling
                .borrow_mut()
                .record_timing("update_egraph_rebuild", rebuild_start.elapsed());
        }
        Ok(())
    }
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
        let profiling = self.profile_costs.then(|| {
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
        let update_start = Instant::now();
        state.update_with_subterms(smt, profiling.as_ref())?;
        if let Some(profiling) = &profiling {
            let mut profiling = profiling.borrow_mut();
            profiling.record_timing("update_with_subterms", update_start.elapsed());
            profiling.set_egraph_after_update(
                state.egraph.number_of_classes(),
                egraph_node_count(&state.egraph),
            );
        }

        let cost_factory_start = Instant::now();
        let cost_fn = F::from_context(smt, state.depth as u32, &self.cost_config);
        if let Some(profiling) = &profiling {
            profiling
                .borrow_mut()
                .record_timing("cost_factory", cost_factory_start.elapsed());
        }

        let saturation_start = Instant::now();
        let saturation = saturate_with_array_types(
            &mut state.egraph,
            cost_fn,
            refinement_step,
            self.term_selection_counts.clone(),
            state.depth,
            &state.array_types,
            ArraySaturationInstrumentation {
                artifact_capture: self.artifact_capture,
                profiling: profiling.clone(),
            },
        );
        if let Some(profiling) = &profiling {
            profiling
                .borrow_mut()
                .record_timing("saturation_total", saturation_start.elapsed());
        }
        state
            .instantiations
            .extend_from_slice(&saturation.instantiations);
        state
            .const_instantiations
            .extend_from_slice(&saturation.const_instantiations);
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
        if let Some(profiling) = profiling {
            if let Ok(profiling) = Rc::try_unwrap(profiling) {
                self.profiling_records.push(profiling.into_inner().finish());
            } else {
                warn!("Unable to unwrap array profiling collector; profiling record dropped");
            }
        }
        if trace_conflicts_enabled() {
            trace!(
                "[yardbird::conflict-trace] sat depth={} refinement_step={} produced regular_insts={} const_insts={} conflicts={} total_regular={} total_const={}",
                state.depth,
                refinement_step,
                saturation.instantiations.len(),
                saturation.const_instantiations.len(),
                saturation.conflicts.len(),
                state.instantiations.len(),
                state.const_instantiations.len()
            );
        }
        Ok(ProofAction::Continue)
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
        let variables = smt.get_variables().to_vec();
        for (term_hash, term) in &const_pairs {
            if trace_instantiations {
                trace!(
                    "[yardbird::inst-trace] const abstract-hash={} abstract-term={}",
                    term_hash,
                    term
                );
            }
            if let Some(inst) =
                UnquantifiedInstantiator::rewrite_unquantified(term.clone(), variables.clone())
            {
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
        let variables = smt.get_variables().to_vec();
        let _ = terms
            .into_iter()
            .flat_map(|(term_hash, term)| {
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] regular abstract-hash={} abstract-term={}",
                        term_hash, term
                    );
                }
                UnquantifiedInstantiator::rewrite_unquantified(term, variables.clone()).map(
                    move |inst| (term_hash.clone(), inst),
                )
            })
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

    fn profiling_enabled(&self) -> bool {
        self.profile_costs
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
            profiling: if self.profile_costs {
                ProfilingRunRecord::enabled(mem::take(&mut self.profiling_records))
            } else {
                ProfilingRunRecord::disabled()
            },
        }
    }
}

impl<F> Abstract<F>
where
    F: ArrayCostFactory + 'static,
{
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
