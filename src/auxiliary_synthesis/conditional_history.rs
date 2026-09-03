use std::collections::HashSet;

use log::{debug, info, warn};

use crate::{
    cost_functions::array::{ArrayCostContext, ArrayCostFactory},
    driver::{self, RefinementContext},
    problem_context::ProblemContext,
    strategies::{ArrayRefinementState, ProofStrategyExt},
    theories::array::{
        array_axioms::translate_term, candidate_scope::CandidateScope,
        instantiation_candidate::InstantiationCandidate,
    },
    utils::run_sequence_smtinterpol,
};

use super::{
    predicate_ast_size, predicate_supports_structural_cost, select_interpolant_guard,
    term_contains_auxiliary_symbol, AuxSynthesisConfig, AuxTriggerState, AuxiliarySpec,
    AuxiliarySynthesisCandidate, GuardPolicy, HistoryCaptureMode, Occurrence, SynthesisTrigger,
};

/// Conditional-history synthesis as a post-refinement driver extension.
///
/// The proof loop only supplies the selected refinements and a refinement
/// context; all synthesis policy remains behind this extension.
pub struct ConditionalHistory<F>
where
    F: ArrayCostFactory,
{
    config: AuxSynthesisConfig,
    cost_config: F::Config,
    trigger_state: AuxTriggerState,
    installed_conflicts: HashSet<String>,
}

impl<F> ConditionalHistory<F>
where
    F: ArrayCostFactory,
{
    pub fn new(config: AuxSynthesisConfig, cost_config: F::Config) -> Self {
        Self {
            config,
            cost_config,
            trigger_state: AuxTriggerState::default(),
            installed_conflicts: HashSet::new(),
        }
    }

    fn handle_instantiations(
        &mut self,
        instantiations: &[InstantiationCandidate],
        depth: u16,
        context: &mut RefinementContext<'_>,
    ) -> driver::Result<()> {
        if self.config.is_off() {
            return Ok(());
        }
        let conflicts = instantiations
            .iter()
            .filter_map(|candidate| candidate.conflict.clone())
            .filter(|conflict| !term_contains_auxiliary_symbol(&conflict.term))
            .collect::<Vec<_>>();
        let ignored = instantiations
            .iter()
            .filter_map(|candidate| candidate.conflict.as_ref())
            .count()
            .saturating_sub(conflicts.len());
        if ignored > 0 {
            info!("AUX-SYNTH ignored {ignored} conflicts containing auxiliary symbols");
        }

        let refinement_step = conflicts
            .first()
            .map(|conflict| conflict.refinement_step)
            .unwrap_or_default();
        let decision = self
            .trigger_state
            .decide(&self.config, &conflicts, refinement_step, 250);
        if decision.detected_conflicts.is_empty() && self.config.trigger == SynthesisTrigger::Detect
        {
            info!(
                "AUX-SYNTH detect depth={} refinement_step={refinement_step}: no non-local conflicts",
                depth
            );
            return Ok(());
        }
        info!(
            "AUX-SYNTH trigger={} guard={} depth={} refinement_step={} fired={} reason={} detected={}",
            self.config.trigger,
            self.config.guard_policy,
            depth,
            refinement_step,
            decision.fired,
            decision.reason,
            decision.detected_conflicts.len()
        );
        for conflict_id in &decision.detected_conflicts {
            if let Some(conflict) = conflicts
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
            return Ok(());
        }
        let Some(selected_conflict_id) = decision.selected_conflict_id else {
            return Ok(());
        };
        if self.installed_conflicts.contains(&selected_conflict_id) {
            return Ok(());
        }
        let Some(conflict) = conflicts
            .iter()
            .find(|conflict| conflict.conflict_id == selected_conflict_id)
        else {
            warn!("AUX-SYNTH selected conflict {selected_conflict_id} was not found");
            return Ok(());
        };
        let candidate = match AuxiliarySynthesisCandidate::from_conflict(
            conflict,
            context.problem().get_variables(),
            self.config.trigger,
            self.config.guard_policy,
        ) {
            Ok(candidate) => candidate,
            Err(error) => {
                warn!(
                    "AUX-SYNTH could not build auxiliary candidate for conflict {}: {error}",
                    conflict.conflict_id
                );
                return Ok(());
            }
        };
        info!(
            "AUX-SYNTH validating candidate from conflict={} against the concrete array theory at depth {}",
            candidate.source_conflict_id(),
            depth
        );
        let concrete_problem = context.validate_spurious_counterexample(depth)?;
        let source_conflict_id = candidate.source_conflict_id().to_string();
        let guard_policy = candidate.guard_policy;
        let spec = match self.synthesize(&candidate, context.problem(), &concrete_problem) {
            Ok(Some(spec)) => spec,
            Ok(None) => {
                info!(
                    "AUX-SYNTH conflict={source_conflict_id} produced no {guard_policy} guard candidate; keeping ordinary refinement"
                );
                return Ok(());
            }
            Err(error) => {
                warn!(
                    "AUX-SYNTH failed for conflict={source_conflict_id}: {error}; keeping ordinary refinement"
                );
                return Ok(());
            }
        };
        info!(
            "AUX-SYNTH synthesized aux_id={} source_conflict={} history={} prophecy={:?}",
            spec.aux_id,
            spec.source_conflict_id,
            spec.history.name,
            spec.prophecy.as_ref().map(|prophecy| prophecy.name.clone())
        );
        self.installed_conflicts.insert(source_conflict_id);
        context.problem_mut().install_auxiliary_specs(vec![spec])?;
        Ok(())
    }

    fn synthesize(
        &self,
        candidate: &AuxiliarySynthesisCandidate,
        abstract_problem: &dyn ProblemContext,
        concrete_problem: &crate::vmt_bmc_session::VmtBmcSession,
    ) -> anyhow::Result<Option<AuxiliarySpec>> {
        match candidate.guard_policy {
            GuardPolicy::True => AuxiliarySpec::from_candidate(candidate).map(Some),
            GuardPolicy::Interpolant => {
                let sequence = run_sequence_smtinterpol(concrete_problem)?;
                info!(
                    "AUX-SYNTH generated {} sequence interpolants with {} predicate candidates at depth {} using {}",
                    sequence.partitions.len(),
                    sequence.predicates.candidates().len(),
                    sequence.depth,
                    sequence.logic,
                );
                for partition in &sequence.partitions {
                    debug!(
                        "AUX-SYNTH interpolant frame={} number={} term={}",
                        partition.frame,
                        partition.interpolant.interpolant_number,
                        partition.interpolant.term,
                    );
                }
                for (index, predicate) in sequence.predicates.candidates().iter().enumerate() {
                    debug!(
                        "AUX-SYNTH predicate candidate={} interpolants={:?} variables={:?} term={}",
                        index, predicate.interpolant_numbers, predicate.variables, predicate.term,
                    );
                }
                let candidates = abstract_problem.get_array_candidate_catalog();
                let cost_context = ArrayCostContext::from_problem(
                    abstract_problem,
                    &candidates,
                    CandidateScope::AllCandidates,
                );
                let mut cost_function =
                    F::from_context(&cost_context, u32::from(sequence.depth), &self.cost_config);
                let ranker = std::any::type_name::<F>()
                    .rsplit("::")
                    .next()
                    .unwrap_or("array-cost");
                let Some(selected) = select_interpolant_guard(
                    candidate,
                    &sequence,
                    abstract_problem,
                    ranker,
                    |guard| match predicate_supports_structural_cost(guard)
                        .then(|| translate_term(guard.clone()))
                        .flatten()
                    {
                        Some(expression) => (cost_function.cost_rec(&expression), true),
                        None => (predicate_ast_size(guard), false),
                    },
                )?
                else {
                    return Ok(None);
                };
                let capture_mode = match selected.occurrence {
                    Occurrence::First => {
                        let latch_name = format!("yb_capture_{}", candidate.aux_id);
                        HistoryCaptureMode::FirstOccurrence {
                            latch_next_name: format!("{latch_name}_next"),
                            latch_name,
                        }
                    }
                    Occurrence::Last => HistoryCaptureMode::LastOccurrence,
                };
                info!(
                    "AUX-SYNTH selected interpolant guard candidate={} derivation={} mode={} cost={} ranker={} structural={} property_overlap={} guard={}",
                    selected.record.predicate_index,
                    selected.record.derivation,
                    selected.record.capture_mode,
                    selected.record.cost,
                    selected.record.ranker,
                    selected.record.structurally_scored,
                    selected.record.property_overlap,
                    selected.capture_guard,
                );
                let mut spec = AuxiliarySpec::from_candidate_with_guard(
                    candidate,
                    selected.capture_guard,
                    capture_mode,
                );
                spec.interpolant_guard_selection = Some(selected.record);
                Ok(Some(spec))
            }
            GuardPolicy::AxiomLocal | GuardPolicy::Llm => Ok(None),
        }
    }
}

impl<F> ProofStrategyExt<ArrayRefinementState> for ConditionalHistory<F>
where
    F: ArrayCostFactory + 'static,
{
    fn refine(
        &mut self,
        state: &mut ArrayRefinementState,
        context: &mut RefinementContext<'_>,
    ) -> driver::Result<()> {
        self.handle_instantiations(&state.candidates, state.depth, context)
    }
}
