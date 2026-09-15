use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    mem,
    rc::Rc,
    time::Instant,
};

use log::{info, trace, warn};
use rustc_hash::FxHashMap;
use smt2parser::{concrete::Term, vmt::VMTModel};

use crate::{
    cost_functions::array::{ArrayCostContext, ArrayCostFactory},
    driver::{self},
    ic3ia::{call_ic3ia, ic3ia_output_contains_proof},
    instantiation_strategy::assertion_tracker::canonical_instantiation_key,
    profiling::{ArrayProfilingCollector, ProfilingRecord, ProfilingRunRecord},
    solver::PropertyCheckMode,
    theories::array::{
        array_axioms::{
            expr_to_term, generate_array_instantiation_candidates_with_budget, ArrayExpr,
            ArrayInstantiationInstrumentation, ArrayInstantiationOptions, ArrayLanguage,
        },
        array_dataflow::{build_property_cone, PropertyCone},
        array_egraph_builder::{
            ArrayEGraphBuildStage, ArrayEGraphBuildStep, ArrayEGraphBuilder,
            SourceThenFullEGraphBuilder,
        },
        array_rule_instantiator::ArrayArtifactCapture,
        encodings::{EncodingOptions, EncodingPlan},
        instantiation_candidate::{InstantiationBatch, InstantiationCandidate},
        instantiation_ranker::{InstantiationRanker, PreferSourceInstantiationRanker},
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
    quantifiers: crate::quantifier_abstraction::QuantifierPlan,
    // Scheduling survives solver checks; model-specific matches live in state.
    binder_next_rule: HashMap<crate::quantifier_abstraction::SearchPhase, usize>,
    quantifier_provenance: crate::quantifier_provenance::QuantifierProvenance,
    configuration_error: Option<String>,
    owns_quantifiers: bool,
    decision_data: Vec<DecisionRecord>,
    abstract_instantiations: Vec<AbstractInstantiationRecord>,
    term_selection_counts: FxHashMap<String, u32>,
    term_selection_decisions: FxHashMap<String, String>,
    artifact_capture: ArrayArtifactCapture,
    profile: bool,
    profiling_records: Vec<ProfilingRecord>,
    egraph_builder: Box<dyn ArrayEGraphBuilder>,
    cone_attempted_depths: HashSet<u16>,
    property_cone: PropertyCone,
    preprocess_exact_read_after_write: bool,
    encoding_options: EncodingOptions,
    encoding_plan: EncodingPlan,
    candidate_winners_per_group: usize,
    instantiation_ranker: Box<dyn InstantiationRanker>,
    property_check_mode: PropertyCheckMode,
}

impl<F> Abstract<F>
where
    F: ArrayCostFactory,
{
    pub fn new(bmc_depth: u16, run_ic3ia: bool, cost_config: F::Config, profile: bool) -> Self {
        Self {
            _bmc_depth: bmc_depth,
            run_ic3ia,
            cost_config,
            discovered_array_types: vec![],
            quantifiers: crate::quantifier_abstraction::QuantifierPlan::default(),
            binder_next_rule: HashMap::new(),
            quantifier_provenance: Default::default(),
            configuration_error: None,
            owns_quantifiers: false,
            decision_data: vec![],
            abstract_instantiations: vec![],
            term_selection_counts: FxHashMap::default(),
            term_selection_decisions: FxHashMap::default(),
            artifact_capture: ArrayArtifactCapture::default(),
            profile,
            profiling_records: vec![],
            egraph_builder: Box::<SourceThenFullEGraphBuilder>::default(),
            cone_attempted_depths: HashSet::new(),
            property_cone: PropertyCone::default(),
            preprocess_exact_read_after_write: false,
            encoding_options: EncodingOptions::default(),
            encoding_plan: EncodingPlan::default(),
            candidate_winners_per_group: 1,
            instantiation_ranker: Box::new(PreferSourceInstantiationRanker),
            property_check_mode: PropertyCheckMode::Scoped,
        }
    }

    pub fn with_artifact_capture(mut self, artifact_capture: ArrayArtifactCapture) -> Self {
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

    pub fn with_recurrent_product_abstraction(mut self, enabled: bool) -> Self {
        self.encoding_options.recurrent_products = enabled;
        self
    }

    pub fn with_guarded_read_updates(mut self, enabled: bool) -> Self {
        self.encoding_options.guarded_read_updates = enabled;
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
    pub(crate) guarded_read_updates: Vec<Term>,
    pub array_types: Vec<(String, String)>,
    pub(crate) egraph_builder: Box<dyn ArrayEGraphBuilder>,
    pub(crate) binder_search: Option<BinderSearchState>,
}

/// One solver model's fixed binder graph and unsuccessful selection passes.
pub(crate) struct BinderSearchState {
    prepared: crate::quantifier_abstraction::PreparedQuantifierSearch,
    empty_passes: HashMap<crate::quantifier_abstraction::SearchPhase, BinderPassContext>,
}

struct BinderPassContext {
    refinement_step: u32,
    selection_counts: FxHashMap<String, u32>,
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
        self.configuration_error = None;
        self.binder_next_rule.clear();
        self.owns_quantifiers = model.as_commands().iter().any(|command| match command {
            smt2parser::concrete::Command::DefineFun { term, .. }
            | smt2parser::concrete::Command::Assert { term } => {
                crate::quantifier_abstraction::contains_binders(term)
            }
            _ => false,
        });
        let model = match crate::quantifier_provenance::scope_model(model.clone(), self.profile) {
            Ok((model, provenance)) => {
                self.quantifier_provenance = provenance;
                model
            }
            Err(error) => {
                self.configuration_error = Some(error.to_string());
                return model;
            }
        };
        let (model, bindings) = model.herbrandize_universal_property_with_bindings();
        self.quantifier_provenance
            .record_property_witnesses(&bindings);
        let herbrand_witnesses = bindings.len();
        if herbrand_witnesses > 0 {
            info!("Herbrandized universal property with {herbrand_witnesses} witness constants");
        }
        let original = model.clone();
        let model = match crate::quantifier_abstraction::lower_model_with_provenance(
            model,
            &mut self.quantifier_provenance,
        ) {
            Ok((model, plan)) => {
                info!(
                    "Abstracted {} quantifier/lambda expressions for Yardbird instantiation",
                    plan.rules.len()
                );
                self.quantifiers = plan;
                model
            }
            Err(error) => {
                self.configuration_error = Some(error.to_string());
                return original;
            }
        };
        let (abstracted_model, discovered_types) =
            model.abstract_array_theory_with_preprocessing(self.preprocess_exact_read_after_write);
        let (abstracted_model, encoding_plan) =
            EncodingPlan::apply(abstracted_model, &discovered_types, self.encoding_options);
        self.encoding_plan = encoding_plan;
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
        !state.candidates.is_empty() || !state.guarded_read_updates.is_empty()
    }

    fn allows_concrete_validation(&self) -> bool {
        !self.owns_quantifiers
    }

    fn configuration_error(&self) -> Option<&str> {
        self.configuration_error.as_deref()
    }

    fn refinement_logic_terms(&self) -> Vec<Term> {
        self.quantifiers
            .rules
            .iter()
            .map(|rule| rule.body.clone())
            .collect()
    }

    fn supports_lambda_abstraction(&self) -> bool {
        true
    }

    fn setup(
        &mut self,
        smt: &dyn crate::problem_context::ProblemContext,
        depth: u16,
    ) -> driver::Result<ArrayRefinementState> {
        let egraph = egg::EGraph::new(());
        let egraph_builder = self
            .egraph_builder
            .clone_for_refinement(&mut self.cone_attempted_depths, depth);
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
            guarded_read_updates: vec![],
            array_types,
            egraph_builder,
            binder_search: None,
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
        let witnesses = self.binder_candidates(
            smt,
            state,
            refinement_step,
            crate::quantifier_abstraction::SearchPhase::Witnesses,
            profiling.clone(),
        )?;
        self.absorb_candidates(state, witnesses);
        if !state.candidates.is_empty() {
            self.finish_profiling_record(profiling);
            return Ok(ProofAction::Continue);
        }
        state.guarded_read_updates = self.encoding_plan.violated_guarded_read_updates(
            smt,
            state.depth,
            self.candidate_winners_per_group,
        );
        if !state.guarded_read_updates.is_empty() {
            info!(
                "Selected {} model-violated guarded read update(s) at depth {}",
                state.guarded_read_updates.len(),
                state.depth
            );
            self.finish_profiling_record(profiling);
            return Ok(ProofAction::Continue);
        }
        if let Some(profiling) = &profiling {
            profiling.borrow_mut().set_egraph_before_update(
                state.egraph.number_of_classes(),
                egraph_node_count(&state.egraph),
            );
        }
        // With no selected instances, the driver calls `sat` again on this
        // model to widen the array graph (after concrete validation when allowed).
        // Keep those stages ahead of term-generating binder expansion.
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
                    let binders = self.binder_candidates(
                        smt,
                        state,
                        refinement_step,
                        crate::quantifier_abstraction::SearchPhase::Expand,
                        profiling.clone(),
                    )?;
                    self.absorb_candidates(state, binders);
                    self.finish_profiling_record(profiling);
                    if !state.candidates.is_empty() {
                        return Ok(ProofAction::Continue);
                    }
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
            let mut seen = HashSet::new();
            let mut accepted_by_rule = HashMap::new();
            let array_candidates = generate_array_instantiation_candidates_with_budget(
                &state.egraph,
                cost_fn.clone(),
                &state.array_types,
                ArrayInstantiationOptions {
                    additional_terms: vec![],
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
                self.candidate_winners_per_group,
                |candidate| {
                    if !self
                        .instantiation_ranker
                        .is_eligible(candidate, expansion.candidate_scope)
                    {
                        return Ok(false);
                    }
                    let rule_kind = candidate.rule.kind();
                    let count = accepted_by_rule.entry(rule_kind).or_insert(0);
                    if *count
                        >= self
                            .instantiation_ranker
                            .source_batch_limit(rule_kind, self.candidate_winners_per_group)
                    {
                        return Ok(false);
                    }
                    let Some(key) = self.installable_expression(smt, &candidate.expression) else {
                        return Ok(false);
                    };
                    if known_instantiations.contains(&key) || seen.contains(&key) {
                        return Ok(false);
                    }
                    if smt
                        .eval_to_string(&expr_to_term(candidate.expression.clone()))?
                        .trim()
                        != "false"
                    {
                        return Ok(false);
                    }
                    seen.insert(key);
                    *count += 1;
                    Ok(true)
                },
            )?;
            candidate_batch.extend(array_candidates.candidates);
            let summary = candidate_batch.prepare_with_ranker(
                expansion.candidate_scope,
                &known_instantiations,
                self.candidate_winners_per_group,
                self.instantiation_ranker.as_ref(),
                |term| smt.eval_to_string(term),
                |candidate| self.installable_expression(smt, &candidate.expression),
            )?;

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

            self.absorb_candidates(state, candidate_batch);

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

            let mut binders = self.binder_candidates(
                smt,
                state,
                refinement_step,
                crate::quantifier_abstraction::SearchPhase::TriggeredConflicts,
                profiling.clone(),
            )?;
            if binders.selected().next().is_none() {
                binders = self.binder_candidates(
                    smt,
                    state,
                    refinement_step,
                    crate::quantifier_abstraction::SearchPhase::Conflicts,
                    profiling.clone(),
                )?;
            }
            self.absorb_candidates(state, binders);

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
        self.encoding_plan
            .install_guarded_read_updates(state.guarded_read_updates, smt);
        let trace_instantiations = trace_instantiations_enabled();
        for candidate in state.candidates {
            let expression = candidate.expression;
            let provenance = candidate.provenance;
            let term_hash = crate::training::canonical_term_hash(&expression);
            let term = expr_to_term(expression);
            let quantifier_kind = candidate.rule.category();
            let rule_name = candidate.rule.name().to_string();

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
            if quantifier_kind == crate::quantified_rule::QuantifiedRuleCategory::InputBinder {
                if let Some(record) = self
                    .profiling_records
                    .last_mut()
                    .filter(|r| r.bmc_depth == Some(state.depth))
                {
                    let counters = &mut record
                        .quantifier_work
                        .entry(rule_name)
                        .or_default()
                        .entry("installation".into())
                        .or_default()
                        .counters;
                    *counters
                        .entry("abstract_instances_added".into())
                        .or_default() += u64::from(result.abstract_instance_added);
                    *counters
                        .entry("indexed_assertions_added".into())
                        .or_default() += result.indexed_assertions_added;
                    *counters
                        .entry("indexed_assertions_deduplicated".into())
                        .or_default() += result.indexed_assertions_deduplicated;
                }
            }
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

    fn quantifier_provenance(&self) -> crate::quantifier_provenance::QuantifierProvenance {
        self.quantifier_provenance.clone()
    }

    fn take_profiling_records(&mut self) -> Vec<ProfilingRecord> {
        mem::take(&mut self.profiling_records)
    }

    fn result(
        &mut self,
        vmt_model: &mut VMTModel,
        smt: &dyn crate::problem_context::ProblemContext,
    ) -> ProofLoopResult {
        for auxiliary_spec in smt.get_auxiliary_specs() {
            auxiliary_spec.apply_to_model(vmt_model);
        }
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
        let mut solver_statistics = smt.get_solver_statistics();
        self.encoding_plan.add_statistics(&mut solver_statistics);
        ProofLoopResult {
            model: Some(vmt_model.clone()),
            used_instances: mem::take(&mut smt.get_instantiations()),
            total_instantiations_added: smt.get_number_instantiations_added(),
            total_refinement_steps: 0,
            solver_statistics,
            counterexample: false,
            found_proof,
            unsat_core: None, // VMT mode unsat core tracked separately via dump-unsat-core
            decision_data: mem::take(&mut self.decision_data),
            abstract_instantiations: mem::take(&mut self.abstract_instantiations),
            indexed_instantiations: vec![],
            unsat_events: vec![],
            auxiliary_records: smt.get_auxiliary_records(),
            run_progress: None,
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

    fn binder_candidates(
        &mut self,
        smt: &dyn crate::problem_context::ProblemContext,
        state: &mut ArrayRefinementState,
        refinement_step: u32,
        phase: crate::quantifier_abstraction::SearchPhase,
        profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
    ) -> anyhow::Result<InstantiationBatch> {
        if self.quantifiers.rules.is_empty() {
            return Ok(InstantiationBatch::default());
        }
        let _phase_guard = profiling
            .as_ref()
            .map(|p| crate::profiling::QuantifierPhaseGuard::new(p.clone(), phase.timing_key()));
        let phase_start = Instant::now();
        if state.binder_search.is_none() {
            let start = Instant::now();
            state.binder_search = Some(BinderSearchState {
                prepared: self.quantifiers.prepare(smt)?,
                empty_passes: HashMap::new(),
            });
            if let Some(profiling) = &profiling {
                let mut profiling = profiling.borrow_mut();
                profiling.record_timing("input_binder_prepare", start.elapsed());
                profiling.add_counter("input_binder_model_preparations", 1);
            }
        }
        let search = state.binder_search.as_mut().unwrap();
        // Widening the array graph leaves the prepared binder graph, model,
        // known instances, cost configuration and ranker unchanged. Only
        // representative-use history may change between these attempts.
        if search.empty_passes.get(&phase).is_some_and(|context| {
            context.refinement_step == refinement_step
                && context.selection_counts == self.term_selection_counts
        }) {
            if let Some(profiling) = &profiling {
                let mut profiling = profiling.borrow_mut();
                profiling.add_counter("input_binder_empty_passes_reused", 1);
                profiling.record_timing(phase.timing_key(), phase_start.elapsed());
            }
            return Ok(InstantiationBatch::default());
        }
        search.empty_passes.remove(&phase);
        let prepared = &mut search.prepared;
        prepared.start_phase(
            phase,
            self.binder_next_rule.get(&phase).copied().unwrap_or(0),
        );
        // Derived terms remain available for witnesses and nested binders.
        // Model-violation eligibility is independent of this vocabulary scope.
        let scope = crate::theories::array::candidate_scope::CandidateScope::AllCandidates;
        let known = smt
            .get_instantiations()
            .iter()
            .map(canonical_instantiation_key)
            .collect();
        loop {
            let mut batch = prepared.candidates(
                |term| smt.eval_to_string(term),
                phase,
                |context| F::from_context(context, state.depth as u32, &self.cost_config),
                ArrayInstantiationOptions {
                    additional_terms: vec![],
                    candidate_catalog: prepared.catalog.clone(),
                    candidate_scope: scope,
                    refinement_step,
                    selection_counts: self.term_selection_counts.clone(),
                    depth: state.depth,
                    instrumentation: ArrayInstantiationInstrumentation {
                        artifact_capture: self.artifact_capture,
                        profiling: profiling.clone(),
                    },
                },
            )?;
            self.binder_next_rule
                .insert(phase, prepared.next_rule_index(phase));
            let selection_start = profiling.as_ref().map(|_| Instant::now());
            let summary = batch.prepare_with_ranker(
                scope,
                &known,
                self.candidate_winners_per_group,
                self.instantiation_ranker.as_ref(),
                |term| smt.eval_to_string(term),
                |candidate| self.installable_expression(smt, &candidate.expression),
            )?;
            if let Some(profiling) = &profiling {
                let mut profiling = profiling.borrow_mut();
                if let Some(start) = selection_start {
                    profiling.record_timing("input_binder_selection", start.elapsed());
                }
                for (rule, counts) in summary.by_rule {
                    profiling.record_rule_candidates(&rule, counts.generated, counts.selected);
                    profiling.record_quantifier_counter(
                        &rule,
                        "known_or_uninstallable_candidates",
                        counts.rejected_known_or_uninstallable as u64,
                    );
                }
                profiling.add_counter(
                    "duplicate_or_uninstallable_instantiations_filtered",
                    summary.rejected_known as u64,
                );
                profiling.add_counter(
                    "instantiation_ranker_candidates_filtered",
                    summary.rejected_ranker as u64,
                );
                profiling.add_counter(
                    "input_binder_instantiations_selected",
                    summary.selected_binders as u64,
                );
            }
            if batch.selected().next().is_some() || !prepared.can_continue(phase) {
                if batch.selected().next().is_none() {
                    // Includes search-budget exhaustion: reuse the bounded
                    // result without claiming that no other matches exist.
                    search.empty_passes.insert(
                        phase,
                        BinderPassContext {
                            refinement_step,
                            selection_counts: self.term_selection_counts.clone(),
                        },
                    );
                }
                if let Some(profiling) = &profiling {
                    profiling
                        .borrow_mut()
                        .record_timing(phase.timing_key(), phase_start.elapsed());
                }
                return Ok(batch);
            }
            // Known/satisfied prefixes must not hide a later usable candidate.
            // Continuations share this model's graph and explicit work bound.
        }
    }

    fn installable_expression(
        &self,
        smt: &dyn crate::problem_context::ProblemContext,
        expression: &ArrayExpr,
    ) -> Option<Term> {
        let term = expr_to_term(expression.clone());
        smt.make_unquantified_instance(term)
            .map(|instance| canonical_instantiation_key(instance.get_term()))
    }

    fn absorb_candidates(&mut self, state: &mut ArrayRefinementState, batch: InstantiationBatch) {
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
            state.candidates.push(candidate);
        }
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::array::{
        array_egraph_builder::{ArrayEGraphExpansion, FullEGraphBuilder},
        candidate_scope::CandidateScope,
    };
    use crate::{
        cost_functions::array::ArrayAstSize, problem_context::ProblemContext,
        quantifier_abstraction::SearchPhase, solver::SolverCheckResult,
        vmt_bmc_session::VmtBmcSession, SolverBackend, YardbirdOptions,
    };

    fn sat_fixture(input: &str) -> (Abstract<ArrayAstSize>, VmtBmcSession) {
        let commands = smt2parser::CommandStream::new(
            std::io::Cursor::new(input.as_bytes()),
            smt2parser::concrete::SyntaxBuilder,
            None,
        )
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
        let model = VMTModel::checked_from(commands).unwrap();
        let mut strategy = Abstract::<ArrayAstSize>::new(1, false, (), false);
        let mut theory: Box<dyn ProofStrategy<'_, ArrayRefinementState>> =
            Box::new(Abstract::<ArrayAstSize>::new(1, false, (), false));
        theory.configure_model(model.clone());
        let model = strategy.configure_model(model);
        let options = YardbirdOptions::from_filename("binder-search.vmt".into());
        let mut smt = VmtBmcSession::new(
            &model,
            &theory,
            SolverBackend::Z3,
            false,
            options.build_instantiation_strategy(),
            false,
            None,
        )
        .unwrap();
        assert_eq!(smt.check_property(), SolverCheckResult::Sat);
        (strategy, smt)
    }

    fn round_robin_fixture() -> (Abstract<ArrayAstSize>, VmtBmcSession) {
        // Both binders stay eligible. No selected batch is installed: this
        // isolates scheduling from changes to eligibility caused by refinement.
        let input = "
            (declare-fun a () (Array Bool Bool))
            (declare-fun p (Bool) Bool)
            (declare-fun q (Bool) Bool)
            (define-fun init () Bool
              (! (and (forall ((x Bool)) (p x))
                      (forall ((y Bool)) (q y))) :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! false :invar-property 0))";
        sat_fixture(input)
    }

    // An empty narrow stage followed by real full construction makes the
    // scheduling boundary independent of source provenance heuristics.
    #[derive(Clone, Debug, Default)]
    struct DeferredFullBuilder {
        source_searched: bool,
        full: FullEGraphBuilder,
    }

    impl ArrayEGraphBuilder for DeferredFullBuilder {
        fn clone_box(&self) -> Box<dyn ArrayEGraphBuilder> {
            Box::new(self.clone())
        }

        fn expand(
            &mut self,
            egraph: &mut egg::EGraph<ArrayLanguage, ()>,
            smt: &dyn crate::problem_context::ProblemContext,
            cone: &PropertyCone,
            depth: u16,
        ) -> anyhow::Result<ArrayEGraphBuildStep> {
            if !self.source_searched {
                self.source_searched = true;
                return Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                    stage: ArrayEGraphBuildStage::Source,
                    candidate_scope: CandidateScope::SourceGroundedOnly,
                    total_subterms: 0,
                    admitted_subterms: 0,
                    newly_admitted_subterms: 0,
                    demand_frontier_sites: 0,
                }));
            }
            self.full.expand(egraph, smt, cone, depth)
        }
    }

    fn expansion_fixture(array_conflict: bool) -> (Abstract<ArrayAstSize>, VmtBmcSession) {
        let extra = if array_conflict {
            "(not (= (select ((as const (Array Bool Bool)) false) true) false))"
        } else {
            "true"
        };
        let (mut strategy, smt) = sat_fixture(&format!(
            "(declare-fun a () (Array Bool Bool))
             (declare-fun p (Bool) Bool)
             (define-fun init () Bool
               (! (and (forall ((x Bool)) (p x)) (p true) (p false) {extra}) :init true))
             (define-fun trans () Bool (! true :trans true))
             (define-fun prop () Bool (! false :invar-property 0))"
        ));
        strategy.egraph_builder = Box::<DeferredFullBuilder>::default();
        (strategy, smt)
    }

    #[test]
    fn binder_expansion_waits_for_all_array_stages() {
        let (mut strategy, smt) = expansion_fixture(false);
        strategy.profile = true;
        let mut state = strategy.setup(&smt, 0).unwrap();
        assert!(!strategy.allows_concrete_validation());
        for _ in 0..2 {
            assert!(matches!(
                strategy.sat(&mut state, &smt, 0).unwrap(),
                ProofAction::Continue
            ));
            assert!(!strategy.has_pending_refinement(&state));
            assert!(!strategy.binder_next_rule.contains_key(&SearchPhase::Expand));
        }
        assert!(matches!(
            strategy.sat(&mut state, &smt, 0).unwrap(),
            ProofAction::Continue
        ));
        assert!(strategy.has_pending_refinement(&state));
        assert!(strategy.binder_next_rule.contains_key(&SearchPhase::Expand));
        assert_eq!(strategy.profiling_records.len(), 3);
        // The full array stage reuses all three unsuccessful binder phases.
        // No rule matching, grounding or model evaluation is repeated there.
        assert!(strategy.profiling_records[1].quantifier_work.is_empty());
        assert_eq!(
            strategy.profiling_records[1].counters["input_binder_empty_passes_reused"],
            3
        );
        assert!(state.candidates.iter().all(|candidate| {
            smt.eval_to_string(&expr_to_term(candidate.expression.clone()))
                .unwrap()
                .trim()
                == "true"
        }));
    }

    #[test]
    fn full_array_conflict_is_selected_before_binder_expansion() {
        let (mut strategy, mut smt) = expansion_fixture(true);
        let mut state = strategy.setup(&smt, 0).unwrap();
        strategy.sat(&mut state, &smt, 0).unwrap();
        assert!(!strategy.has_pending_refinement(&state));
        strategy.sat(&mut state, &smt, 0).unwrap();
        assert!(strategy.has_pending_refinement(&state));
        assert!(!strategy.binder_next_rule.contains_key(&SearchPhase::Expand));
        assert!(state.candidates.iter().all(|candidate| {
            !candidate.rule.name().starts_with("input-binder-")
                && smt
                    .eval_to_string(&expr_to_term(candidate.expression.clone()))
                    .unwrap()
                    .trim()
                    == "false"
        }));
        strategy.finish(state, &mut smt).unwrap();
        assert_eq!(smt.check_property(), SolverCheckResult::Unsat);
    }

    #[test]
    fn exhausted_array_and_binder_search_terminates() {
        let (mut strategy, smt) = sat_fixture(
            "(declare-fun a () (Array Bool Bool))
             (define-fun init () Bool (! true :init true))
             (define-fun trans () Bool (! true :trans true))
             (define-fun prop () Bool (! false :invar-property 0))",
        );
        strategy.egraph_builder = Box::<DeferredFullBuilder>::default();
        strategy.profile = true;
        let mut state = strategy.setup(&smt, 0).unwrap();
        for _ in 0..2 {
            strategy.sat(&mut state, &smt, 0).unwrap();
            assert!(!strategy.has_pending_refinement(&state));
        }
        assert!(matches!(
            strategy.sat(&mut state, &smt, 0),
            Err(driver::Error::AbstractionExhausted { depth: 0 })
        ));
        assert_eq!(strategy.profiling_records.len(), 3);
    }

    fn profiled_binder_pass(
        strategy: &mut Abstract<ArrayAstSize>,
        state: &mut ArrayRefinementState,
        smt: &VmtBmcSession,
        phase: SearchPhase,
        step: u32,
    ) -> ProfilingRecord {
        let profiling = Rc::new(RefCell::new(ArrayProfilingCollector::new(
            "test",
            Some(state.depth),
            Some(step),
            vec![],
        )));
        let batch = strategy
            .binder_candidates(smt, state, step, phase, Some(profiling.clone()))
            .unwrap();
        assert!(batch.selected().next().is_none());
        Rc::try_unwrap(profiling)
            .unwrap_or_else(|_| panic!("profiling collector still borrowed"))
            .into_inner()
            .finish()
    }

    #[test]
    fn empty_binder_pass_reuse_respects_selection_context_and_phase() {
        let (mut strategy, smt) = expansion_fixture(false);
        let mut state = strategy.setup(&smt, 0).unwrap();
        let first =
            profiled_binder_pass(&mut strategy, &mut state, &smt, SearchPhase::Conflicts, 0);
        assert!(first.rule_instantiation.rule_search_calls > 0);
        let repeated =
            profiled_binder_pass(&mut strategy, &mut state, &smt, SearchPhase::Conflicts, 0);
        assert_eq!(repeated.rule_instantiation.rule_search_calls, 0);
        assert_eq!(repeated.counters["input_binder_empty_passes_reused"], 1);

        let other_phase = profiled_binder_pass(
            &mut strategy,
            &mut state,
            &smt,
            SearchPhase::TriggeredConflicts,
            0,
        );
        assert!(other_phase.rule_instantiation.rule_search_calls > 0);
        strategy.term_selection_counts.insert(
            crate::training::canonical_term_hash(&"true".parse().unwrap()),
            1,
        );
        let changed_history =
            profiled_binder_pass(&mut strategy, &mut state, &smt, SearchPhase::Conflicts, 0);
        assert!(changed_history.rule_instantiation.rule_search_calls > 0);
        let changed_step =
            profiled_binder_pass(&mut strategy, &mut state, &smt, SearchPhase::Conflicts, 1);
        assert!(changed_step.rule_instantiation.rule_search_calls > 0);
    }

    #[test]
    fn empty_binder_pass_is_not_reused_after_a_solver_check() {
        let (mut strategy, mut smt) = expansion_fixture(false);
        let mut state = strategy.setup(&smt, 0).unwrap();
        profiled_binder_pass(&mut strategy, &mut state, &smt, SearchPhase::Conflicts, 0);
        assert_eq!(smt.check_property(), SolverCheckResult::Sat);
        let mut next_state = strategy.setup(&smt, 0).unwrap();
        let fresh = profiled_binder_pass(
            &mut strategy,
            &mut next_state,
            &smt,
            SearchPhase::Conflicts,
            0,
        );
        assert!(fresh.rule_instantiation.rule_search_calls > 0);
        assert!(!fresh
            .counters
            .contains_key("input_binder_empty_passes_reused"));
    }

    #[test]
    fn binder_round_robin_survives_new_models_and_phase_reentry() {
        for fresh_model in [false, true] {
            let (mut strategy, mut smt) = round_robin_fixture();
            let names = strategy
                .quantifiers
                .rules
                .iter()
                .map(|rule| format!("input-binder-{}", rule.name))
                .collect::<Vec<_>>();
            assert_eq!(names.len(), 2);
            let mut state = strategy.setup(&smt, 0).unwrap();
            for step in 0..4 {
                if fresh_model {
                    assert_eq!(smt.check_property(), SolverCheckResult::Sat);
                    state = strategy.setup(&smt, 0).unwrap();
                    assert!(state.binder_search.is_none());
                }
                let batch = strategy
                    .binder_candidates(&smt, &mut state, step, SearchPhase::Conflicts, None)
                    .unwrap();
                let selected = batch.selected().collect::<Vec<_>>();
                assert_eq!(selected.len(), 1);
                assert_eq!(selected[0].rule.name(), names[step as usize % 2]);
            }
        }
    }

    #[test]
    fn binder_round_robin_keeps_phase_positions_independent() {
        let (mut strategy, smt) = round_robin_fixture();
        let names = strategy
            .quantifiers
            .rules
            .iter()
            .map(|rule| format!("input-binder-{}", rule.name))
            .collect::<Vec<_>>();
        let mut state = strategy.setup(&smt, 0).unwrap();
        for (phase, expected) in [
            (SearchPhase::Conflicts, 0),
            (SearchPhase::Expand, 0),
            (SearchPhase::Conflicts, 1),
            (SearchPhase::Expand, 1),
        ] {
            let batch = strategy
                .binder_candidates(&smt, &mut state, 0, phase, None)
                .unwrap();
            assert_eq!(
                batch.selected().next().unwrap().rule.name(),
                names[expected]
            );
        }
    }
}
