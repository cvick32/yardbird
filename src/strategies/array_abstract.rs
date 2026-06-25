use std::{collections::HashSet, mem};

use log::{info, trace, warn};
use smt2parser::{
    concrete::Term,
    vmt::{quantified_instantiator::UnquantifiedInstantiator, VMTModel},
};

use crate::{
    auxiliary_synthesis::{
        term_contains_auxiliary_symbol, ArrayConflictRecord, AuxSynthesisConfig, AuxTriggerState,
        AuxiliarySpec, SynthesisTrigger,
    },
    cost_functions::YardbirdCostFunction,
    driver::{self},
    ic3ia::{call_ic3ia, ic3ia_output_contains_proof},
    solver_interface::SolverInterface,
    theories::array::{
        array_axioms::{
            expr_to_term, saturate_with_array_types, translate_term, ArrayExpr, ArrayLanguage,
        },
        array_conflict_scheduler::preprocess_array_expr,
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
    F: YardbirdCostFunction<ArrayLanguage>,
{
    const_instantiations: Vec<Term>,
    _bmc_depth: u16,
    run_ic3ia: bool,
    cost_fn_factory: fn(&dyn SolverInterface, u32) -> F,
    discovered_array_types: Vec<(String, String)>,
    decision_data: Vec<DecisionRecord>,
    abstract_instantiations: Vec<AbstractInstantiationRecord>,
    aux_config: AuxSynthesisConfig,
    aux_trigger_state: AuxTriggerState,
    pending_aux_specs: Vec<AuxiliarySpec>,
    installed_aux_conflicts: HashSet<String>,
    aux_covered_term_hashes: HashSet<String>,
}

impl<F> Abstract<F>
where
    F: YardbirdCostFunction<ArrayLanguage>,
{
    pub fn new(
        bmc_depth: u16,
        run_ic3ia: bool,
        cost_fn_factory: fn(&dyn SolverInterface, u32) -> F,
        aux_config: AuxSynthesisConfig,
    ) -> Self {
        Self {
            _bmc_depth: bmc_depth,
            run_ic3ia,
            aux_config,
            const_instantiations: vec![],
            cost_fn_factory,
            discovered_array_types: vec![],
            decision_data: vec![],
            abstract_instantiations: vec![],
            aux_trigger_state: AuxTriggerState::default(),
            pending_aux_specs: vec![],
            installed_aux_conflicts: HashSet::new(),
            aux_covered_term_hashes: HashSet::new(),
        }
    }
}

/// State for the inner refinement looop
pub struct ArrayRefinementState {
    pub depth: u16,
    pub egraph: egg::EGraph<ArrayLanguage, ()>,
    pub instantiations: Vec<ArrayExpr>,
    pub const_instantiations: Vec<ArrayExpr>,
    pub conflict_records: Vec<ArrayConflictRecord>,
    pub array_types: Vec<(String, String)>,
}

impl ArrayRefinementState {
    pub fn update_with_subterms(
        &mut self,
        smt: &dyn crate::solver_interface::SolverInterface,
    ) -> anyhow::Result<()> {
        for term in smt.get_all_subterms() {
            let interp_str = smt.eval_to_string(term)?;
            let term_id = self.egraph.add_expr(&translate_term(term.clone()).unwrap());
            let preprocessed = preprocess_array_expr(&interp_str);
            let interp_id = self.egraph.add_expr(&preprocessed.parse()?);
            self.egraph.union(term_id, interp_id);
        }
        self.egraph.rebuild();
        Ok(())
    }
}

impl<F> ProofStrategy<'_, ArrayRefinementState> for Abstract<F>
where
    F: YardbirdCostFunction<ArrayLanguage> + 'static,
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
        smt: &dyn crate::solver_interface::SolverInterface,
        depth: u16,
    ) -> driver::Result<ArrayRefinementState> {
        let egraph = egg::EGraph::new(());
        // Use discovered_array_types if available (VMT mode via configure_model),
        // otherwise get from SolverInterface (SMTLIB mode)
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
            conflict_records: vec![],
            array_types,
        })
    }

    fn unsat(
        &mut self,
        state: &mut ArrayRefinementState,
        _solver: &dyn crate::solver_interface::SolverInterface,
    ) -> driver::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut ArrayRefinementState,
        smt: &dyn crate::solver_interface::SolverInterface,
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
        state.update_with_subterms(smt)?;
        let cost_fn = (self.cost_fn_factory)(smt, state.depth as u32);
        let (insts, const_insts, conflicts, decisions, abstract_instantiations) =
            saturate_with_array_types(
                &mut state.egraph,
                cost_fn,
                refinement_step,
                state.depth,
                &state.array_types,
            );
        state.instantiations.extend_from_slice(&insts);
        state.const_instantiations.extend_from_slice(&const_insts);
        state.conflict_records.extend(conflicts.clone());
        self.decision_data.extend(decisions);
        self.abstract_instantiations.extend(abstract_instantiations);
        self.handle_aux_synthesis_detection(state, smt, &conflicts, refinement_step);
        if trace_conflicts_enabled() {
            trace!(
                "[yardbird::conflict-trace] sat depth={} refinement_step={} produced regular_insts={} const_insts={} conflicts={} total_regular={} total_const={}",
                state.depth,
                refinement_step,
                insts.len(),
                const_insts.len(),
                conflicts.len(),
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
        smt: &mut dyn crate::solver_interface::SolverInterface,
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

    fn result(
        &mut self,
        vmt_model: &mut VMTModel,
        smt: &dyn crate::solver_interface::SolverInterface,
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
        }
    }
}

impl<F> Abstract<F>
where
    F: YardbirdCostFunction<ArrayLanguage> + 'static,
{
    fn handle_aux_synthesis_detection(
        &mut self,
        state: &ArrayRefinementState,
        smt: &dyn crate::solver_interface::SolverInterface,
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
