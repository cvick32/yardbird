use std::{cell::RefCell, collections::HashSet, mem, rc::Rc, time::Instant};

use log::{info, trace, warn};
use rustc_hash::FxHashMap;
use smt2parser::{concrete::Term, vmt::VMTModel};

use crate::ic3ia::{call_ic3ia, ic3ia_output_contains_proof};
use crate::policy::effort::{
    EffortContext, EffortDecision, EffortEvent, EffortOperation, EffortRecord, OperationId,
    OperationKind, WorkReport,
};
use crate::policy::term_selection::TermCostFactory;
use crate::policy::YardbirdPolicy;
use crate::profiling::{ProfilingRecord, ProfilingRunRecord, RefinementProfilingCollector};
use crate::rule_matching::candidate::{InstantiationBatch, InstantiationCandidate};
use crate::rule_matching::candidate_builder::ArtifactCapture;
use crate::solver::PropertyCheckMode;
use crate::terms::language::{expr_to_term, TermLanguage};
use crate::theories::array::array_egraph_builder::{
    ArrayEGraphBuildStage, ArrayEGraphBuildStep, ArrayEGraphBuilder,
};
use crate::theories::array::encodings::EncodingOptions;
use crate::theory_support::{ArrayTheorySupport, TheorySupport};
use crate::training::{AbstractInstantiationRecord, DecisionRecord};
use crate::{driver, ProofLoopResult};

use crate::rule_matching::search_context::SearchContext;
use crate::theories::array::refinement::ArrayRefinement;
use crate::theories::quantifiers::refinement::{BinderSearchState, QuantifierRefinement};

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
    F: TermCostFactory,
{
    _bmc_depth: u16,
    run_ic3ia: bool,
    policy: YardbirdPolicy<F>,
    eager: Option<Box<dyn super::eager::InstanceSeeder>>,
    model_sequence: u64,
    offer_sequence: u64,
    array: ArrayRefinement,
    quantifier: QuantifierRefinement,
    decision_data: Vec<DecisionRecord>,
    abstract_instantiations: Vec<AbstractInstantiationRecord>,
    term_selection_counts: FxHashMap<String, u32>,
    term_selection_decisions: FxHashMap<String, String>,
    artifact_capture: ArtifactCapture,
    profile: bool,
    profiling_records: Vec<ProfilingRecord>,
    cone_attempted_depths: HashSet<u16>,
    preprocess_exact_read_after_write: bool,
    encoding_options: EncodingOptions,
    property_check_mode: PropertyCheckMode,
}

impl<F> Abstract<F>
where
    F: TermCostFactory + 'static,
{
    pub fn new(bmc_depth: u16, run_ic3ia: bool, policy: YardbirdPolicy<F>, profile: bool) -> Self {
        Self {
            _bmc_depth: bmc_depth,
            run_ic3ia,
            eager: policy.eager_seeder(),
            policy,
            model_sequence: 0,
            offer_sequence: 0,
            array: ArrayRefinement::default(),
            quantifier: QuantifierRefinement::default(),
            decision_data: vec![],
            abstract_instantiations: vec![],
            term_selection_counts: FxHashMap::default(),
            term_selection_decisions: FxHashMap::default(),
            artifact_capture: ArtifactCapture::default(),
            profile,
            profiling_records: vec![],
            cone_attempted_depths: HashSet::new(),
            preprocess_exact_read_after_write: false,
            encoding_options: EncodingOptions::default(),
            property_check_mode: PropertyCheckMode::Scoped,
        }
    }

    pub fn with_artifact_capture(mut self, artifact_capture: ArtifactCapture) -> Self {
        self.artifact_capture = artifact_capture;
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

    pub fn with_property_check_mode(mut self, mode: PropertyCheckMode) -> Self {
        self.property_check_mode = mode;
        self
    }
}

fn egraph_node_count<N>(egraph: &egg::EGraph<TermLanguage, N>) -> usize
where
    N: egg::Analysis<TermLanguage>,
{
    egraph.classes().map(|class| class.nodes.len()).sum()
}

/// Coordinator-owned state for one solver model. Searches reuse it during staged
/// expansion; a fresh setup discards both modules' model-dependent caches.
/// Both modules borrow this graph. Staged admission and all graph mutation occur
/// between searches; a new model receives a fresh graph and search caches.
pub struct RefinementState {
    pub depth: u16,
    pub egraph: crate::refinement_graph::RefinementGraph,
    pub candidates: Vec<InstantiationCandidate>,
    pub(crate) guarded_read_updates: Vec<Term>,
    pub array_types: Vec<(String, String)>,
    pub(crate) egraph_builder: Box<dyn ArrayEGraphBuilder>,
    pub(crate) binder_search: Option<BinderSearchState>,
    pub(crate) model_version: u64,
    pub(crate) graph_version: u64,
    pub(crate) array_expansion:
        Option<crate::theories::array::array_egraph_builder::ArrayEGraphExpansion>,
    pub(crate) array_exhausted: bool,
    pub(crate) model_reported: bool,
}

impl RefinementState {
    fn grow_vocabulary(
        &mut self,
        smt: &dyn crate::problem_context::ProblemContext,
        budget: usize,
    ) -> anyhow::Result<WorkReport> {
        let growth = self.egraph.grow_vocabulary(smt, budget)?;
        // Revisiting an existing symbolic root can still add model literals or
        // equivalences. Root-count growth alone is not a graph mutation test.
        if growth.examined > 0 {
            self.graph_version += 1;
        }
        Ok(WorkReport {
            vocabulary_work: growth.examined,
            terms_added: growth.added,
            ..Default::default()
        })
    }

    fn expand_array_graph(
        &mut self,
        smt: &dyn crate::problem_context::ProblemContext,
        cone: &crate::theories::array::array_dataflow::PropertyCone,
        profiling: &Option<Rc<RefCell<RefinementProfilingCollector>>>,
    ) -> anyhow::Result<ArrayEGraphBuildStep> {
        if let Some(profiling) = profiling {
            profiling.borrow_mut().set_egraph_before_update(
                self.egraph.number_of_classes(),
                egraph_node_count(&self.egraph),
            );
        }
        let build_start = Instant::now();
        let build_step = self
            .egraph_builder
            .expand(&mut self.egraph, smt, cone, self.depth)?;
        if let ArrayEGraphBuildStep::Expanded(expansion) = &build_step {
            self.graph_version += 1;
            self.array_expansion = Some(*expansion);
            if let Some(profiling) = profiling {
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
                    self.egraph.number_of_classes(),
                    egraph_node_count(&self.egraph),
                );
            }
        }
        self.array_exhausted = matches!(build_step, ArrayEGraphBuildStep::Exhausted);
        Ok(build_step)
    }
}

impl<F> ProofStrategy<'_, RefinementState> for Abstract<F>
where
    F: TermCostFactory + 'static,
{
    fn refinement_limit(&self) -> Option<u32> {
        None
    }

    fn get_theory_support(&self) -> Box<dyn TheorySupport> {
        Box::new(ArrayTheorySupport::new(self.array.array_types.clone()))
    }

    fn property_check_mode(&self) -> PropertyCheckMode {
        self.property_check_mode
    }

    fn instance_seeder(&mut self) -> Option<&mut (dyn super::eager::InstanceSeeder + '_)> {
        match self.eager.as_mut() {
            Some(seeder) => Some(seeder.as_mut()),
            None => None,
        }
    }

    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        let model = if let Some(seeder) = &mut self.eager {
            seeder.configure_vmt(model, true, true)
        } else {
            model
        };
        self.policy.effort_mut().observe(&EffortEvent::NewProblem);
        let model = self.quantifier.configure_model(model, self.profile);
        if self.quantifier.configuration_error.is_some() {
            return model;
        }
        self.array.configure_model(
            model,
            self.preprocess_exact_read_after_write,
            self.encoding_options,
            self.policy.effort().requires_property_cone(),
        )
    }

    fn preprocess_exact_read_after_write(&self) -> bool {
        self.preprocess_exact_read_after_write
    }

    fn has_pending_refinement(&self, state: &RefinementState) -> bool {
        !state.candidates.is_empty() || !state.guarded_read_updates.is_empty()
    }

    fn allows_concrete_validation(&self) -> bool {
        !self.quantifier.owns_quantifiers
    }

    fn configuration_error(&self) -> Option<&str> {
        self.quantifier.configuration_error.as_deref()
    }

    fn refinement_logic_terms(&self) -> Vec<Term> {
        self.quantifier
            .plan
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
    ) -> driver::Result<RefinementState> {
        let egraph =
            crate::refinement_graph::RefinementGraph::new(self.quantifier.plan.signatures.clone());
        let egraph_builder = self
            .policy
            .effort()
            .egraph_builder()
            .clone_for_refinement(&mut self.cone_attempted_depths, depth);
        // Use discovered_array_types if available (VMT mode via configure_model),
        // otherwise get from ProblemContext (SMTLIB mode)
        let array_types = if self.array.array_types.is_empty() {
            smt.get_array_types()
        } else {
            self.array.array_types.clone()
        };
        self.model_sequence += 1;
        Ok(RefinementState {
            model_version: self.model_sequence,
            graph_version: 0,
            array_expansion: None,
            array_exhausted: false,
            model_reported: false,
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
        state: &mut RefinementState,
        _solver: &dyn crate::problem_context::ProblemContext,
    ) -> driver::Result<ProofAction> {
        self.policy
            .effort_mut()
            .observe(&EffortEvent::SolverResult {
                depth: state.depth,
                result: "unsat",
            });
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn unknown(
        &mut self,
        state: &mut RefinementState,
        smt: &dyn crate::problem_context::ProblemContext,
    ) -> driver::Result<ProofAction> {
        self.policy
            .effort_mut()
            .observe(&EffortEvent::SolverResult {
                depth: state.depth,
                result: "unknown",
            });
        Err(driver::Error::SolverUnknown(smt.get_reason_unknown()))
    }

    fn sat(
        &mut self,
        state: &mut RefinementState,
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
        if !state.model_reported {
            self.policy
                .effort_mut()
                .observe(&EffortEvent::SolverResult {
                    depth: state.depth,
                    result: "sat",
                });
            state.model_reported = true;
        }
        let profiling = self.profile.then(|| {
            Rc::new(RefCell::new(RefinementProfilingCollector::new(
                "array_refinement",
                Some(state.depth),
                Some(refinement_step),
                state.array_types.clone(),
            )))
        });
        self.policy.effort_mut().observe(&EffortEvent::BeginPass {
            model: state.model_version,
            depth: state.depth,
            refinement_step,
        });
        let pass_result = (|| loop {
            if state.binder_search.is_some() {
                self.quantifier.prepare_binder_search(
                    smt,
                    &mut state.binder_search,
                    &mut state.egraph,
                    &mut state.graph_version,
                    &profiling,
                )?;
            }
            self.offer_sequence += 1;
            let mut kinds = Vec::new();
            if !self.quantifier.plan.rules.is_empty() {
                kinds.push((
                    OperationKind::DiscoverDependencies,
                    "discover dependency paths".into(),
                ));
                if let Some(search) = &state.binder_search {
                    for (i, request) in search.requests.iter().enumerate() {
                        kinds.push((
                            OperationKind::DependencyRequest(i),
                            request.description.clone(),
                        ));
                    }
                }
                for phase in [
                    crate::theories::quantifiers::SearchPhase::Witnesses,
                    crate::theories::quantifiers::SearchPhase::TriggeredConflicts,
                    crate::theories::quantifiers::SearchPhase::Conflicts,
                    crate::theories::quantifiers::SearchPhase::Expand,
                ] {
                    kinds.push((OperationKind::Binder(phase), format!("{phase:?}")));
                }
            }
            kinds.push((
                OperationKind::GrowVocabulary,
                "grow shared vocabulary".into(),
            ));
            kinds.push((
                OperationKind::GuardedReads,
                "guarded read consequences".into(),
            ));
            if !state.array_exhausted {
                kinds.push((OperationKind::ExpandArray, "expand array vocabulary".into()));
            }
            if state.array_expansion.is_some() {
                kinds.push((
                    OperationKind::ArrayCandidates,
                    "array axiom instances".into(),
                ));
            }
            let operations = kinds
                .into_iter()
                .enumerate()
                .map(|(index, (kind, description))| EffortOperation {
                    id: OperationId {
                        model: state.model_version,
                        offer: self.offer_sequence,
                        index,
                    },
                    kind,
                    description,
                })
                .collect::<Vec<_>>();
            let graph_version_before = state.graph_version;
            let pending_count = state.candidates.len() + state.guarded_read_updates.len();
            let choice_start = self.profile.then(Instant::now);
            let decision = self.policy.effort_mut().choose(&EffortContext {
                model: state.model_version,
                graph_version: state.graph_version,
                depth: state.depth,
                refinement_step,
                pending_instances: state.candidates.len() + state.guarded_read_updates.len(),
                operations: &operations,
            });
            let choice_elapsed_secs = choice_start
                .map(|start| start.elapsed().as_secs_f64())
                .unwrap_or_default();
            let EffortDecision::Execute {
                operation,
                allowance,
            } = decision
            else {
                if let Some(profiling) = &profiling {
                    profiling.borrow_mut().record_effort(EffortRecord {
                        model_version: state.model_version,
                        graph_version_before,
                        graph_version: state.graph_version,
                        pending_instances: pending_count,
                        kind: crate::policy::effort::EffortRecordKind::ReturnToDriver,
                        operation_id: None,
                        operation: "ReturnToDriver".into(),
                        chosen: "ReturnToDriver".into(),
                        offered: operations
                            .iter()
                            .map(|o| o.description.clone())
                            .chain(std::iter::once("ReturnToDriver".into()))
                            .collect(),
                        allowance: None,
                        report: WorkReport::default(),
                        candidates: Vec::new(),
                        choice_elapsed_secs,
                        elapsed_secs: 0.0,
                    });
                }
                return Ok(ProofAction::Continue);
            };
            let operation = operations
                .iter()
                .find(|o| o.id == operation)
                .ok_or_else(|| {
                    anyhow::anyhow!("effort selected a stale or unavailable operation")
                })?;
            allowance.validate()?;
            let start = Instant::now();
            if matches!(
                operation.kind,
                OperationKind::DiscoverDependencies
                    | OperationKind::DependencyRequest(_)
                    | OperationKind::Binder(_)
            ) {
                self.quantifier.prepare_binder_search(
                    smt,
                    &mut state.binder_search,
                    &mut state.egraph,
                    &mut state.graph_version,
                    &profiling,
                )?;
            }
            let pending_instances = state.candidates.iter().filter_map(|candidate| {
                smt.make_unquantified_instance(expr_to_term(candidate.expression.clone()))
                    .map(|instance| crate::instance_installation::assertion_tracker::canonical_instantiation_key(instance.get_term()))
            }).collect::<HashSet<_>>();
            let (term_config, ranker, effort) = self.policy.parts();
            let context = SearchContext::<F> {
                graph: &state.egraph,
                graph_version: state.graph_version,
                smt,
                term_config,
                ranker,
                allowance,
                operation_id: Some(operation.id),
                pending_instances: &pending_instances,
                selection_counts: &self.term_selection_counts,
                artifact_capture: self.artifact_capture,
                depth: state.depth,
                refinement_step,
                profiling: profiling.clone(),
            };
            let mut batch = InstantiationBatch::default();
            let mut report = WorkReport::default();
            let mut retain = false;
            match operation.kind {
                OperationKind::DiscoverDependencies => {
                    report = self
                        .quantifier
                        .discover(&mut state.binder_search, &context)?;
                }
                OperationKind::DependencyRequest(i) => {
                    batch = self.quantifier.dependency_request(
                        &mut state.binder_search,
                        i,
                        &context,
                    )?;
                    report = WorkReport::from_batch(&batch);
                    retain = report.selected > 0;
                }
                OperationKind::Binder(phase) => {
                    batch = self.quantifier.candidates(
                        &mut state.binder_search,
                        phase,
                        &context,
                        effort,
                    )?;
                    report = WorkReport::from_batch(&batch);
                    retain = report.selected > 0
                        || phase != crate::theories::quantifiers::SearchPhase::TriggeredConflicts;
                }
                OperationKind::GuardedReads => {
                    let mut updates = self.array.encoding_plan.violated_guarded_read_updates(
                        smt,
                        state.depth,
                        allowance.winners,
                    );
                    updates.retain(|update| !state.guarded_read_updates.contains(update));
                    report.candidates_returned = updates.len();
                    report.selected = updates.len();
                    state.guarded_read_updates.extend(updates);
                }
                OperationKind::GrowVocabulary => {
                    report = state.grow_vocabulary(smt, allowance.vocabulary_work)?;
                }
                OperationKind::ExpandArray => {
                    report.array_exhausted = matches!(
                        state.expand_array_graph(smt, &self.array.property_cone, &profiling)?,
                        ArrayEGraphBuildStep::Exhausted
                    );
                }
                OperationKind::ArrayCandidates => {
                    batch = self.array.candidates(
                        &state.egraph,
                        &state.array_types,
                        &state.array_expansion.unwrap(),
                        &context,
                    )?;
                    report = WorkReport::from_batch(&batch);
                    retain = true;
                }
            }
            self.policy.effort_mut().observe(&EffortEvent::Completed {
                operation: operation.kind,
                report: &report,
            });
            if let Some(profiling) = &profiling {
                profiling.borrow_mut().record_effort(EffortRecord {
                    model_version: state.model_version,
                    graph_version_before,
                    graph_version: state.graph_version,
                    pending_instances: pending_count,
                    kind: crate::policy::effort::EffortRecordKind::Operation,
                    operation_id: Some(operation.id),
                    operation: format!("{:?}", operation.kind),
                    chosen: operation.description.clone(),
                    candidates: crate::policy::effort::EffortCandidate::from_batch(&batch),
                    offered: operations
                        .iter()
                        .map(|o| o.description.clone())
                        .chain(std::iter::once("ReturnToDriver".into()))
                        .collect(),
                    allowance: Some(allowance),
                    report,
                    choice_elapsed_secs,
                    elapsed_secs: start.elapsed().as_secs_f64(),
                });
            }
            if retain {
                self.absorb_candidates(state, batch);
            }
        })();
        self.finish_profiling_record(profiling);
        pass_result
    }

    #[allow(clippy::unnecessary_fold)]
    fn finish(
        &mut self,
        state: RefinementState,
        smt: &mut dyn crate::problem_context::ProblemContext,
    ) -> driver::Result<()> {
        let installations = self.array.encoding_plan.install_guarded_read_updates(
            state.guarded_read_updates,
            smt,
            self.profile,
        );
        if let Some(record) = self.profiling_records.last_mut() {
            record.installations.extend(installations);
        }
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

            if self.profile {
                if let Some(record) = self.profiling_records.last_mut() {
                    record
                        .installations
                        .push(crate::profiling::InstallationRecord {
                            abstract_instantiation_id: Some(abstract_id.clone()),
                            term: term.to_string(),
                            result: None,
                        });
                }
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
            if let Some(record) = self
                .profiling_records
                .last_mut()
                .and_then(|r| r.installations.last_mut())
            {
                record.result = Some(result);
            }
            self.policy.effort_mut().observe(&EffortEvent::Installed {
                abstract_id: &abstract_id,
                assertions_added: result.solver_assertions_added(),
            });
            if quantifier_kind == crate::rule_matching::rule::QuantifiedRuleCategory::InputBinder {
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

    fn quantifier_provenance(
        &self,
    ) -> crate::theories::quantifiers::provenance::QuantifierProvenance {
        self.quantifier.provenance.clone()
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
        self.array
            .encoding_plan
            .add_statistics(&mut solver_statistics);
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
    F: TermCostFactory + 'static,
{
    fn record_installation_outcome(
        &mut self,
        abstract_instantiation_id: &str,
        result: crate::instance_installation::request::InstantiationInstallResult,
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

    #[cfg(test)]
    fn dependency_candidates(
        &mut self,
        smt: &dyn crate::problem_context::ProblemContext,
        state: &mut RefinementState,
        refinement_step: u32,
        profiling: Option<Rc<RefCell<RefinementProfilingCollector>>>,
    ) -> anyhow::Result<InstantiationBatch> {
        self.policy.effort_mut().observe(&EffortEvent::BeginPass {
            model: state.model_version,
            depth: state.depth,
            refinement_step,
        });
        loop {
            self.offer_sequence += 1;
            let mut kinds = Vec::new();
            if !state
                .binder_search
                .as_ref()
                .is_some_and(|s| s.dependencies_searched)
            {
                kinds.push(OperationKind::DiscoverDependencies);
            }
            if let Some(s) = &state.binder_search {
                kinds.extend((0..s.requests.len()).map(OperationKind::DependencyRequest));
            }
            let operations = kinds
                .into_iter()
                .enumerate()
                .map(|(index, kind)| EffortOperation {
                    id: OperationId {
                        model: state.model_version,
                        offer: self.offer_sequence,
                        index,
                    },
                    kind,
                    description: String::new(),
                })
                .collect::<Vec<_>>();
            let EffortDecision::Execute {
                operation,
                allowance,
            } = self.policy.effort_mut().choose(&EffortContext {
                model: state.model_version,
                graph_version: state.graph_version,
                depth: state.depth,
                refinement_step,
                pending_instances: 0,
                operations: &operations,
            })
            else {
                return Ok(InstantiationBatch::default());
            };
            let kind = operations.iter().find(|o| o.id == operation).unwrap().kind;
            self.quantifier.prepare_binder_search(
                smt,
                &mut state.binder_search,
                &mut state.egraph,
                &mut state.graph_version,
                &profiling,
            )?;
            let (term_config, ranker, _) = self.policy.parts();
            let context = SearchContext::<F> {
                graph: &state.egraph,
                graph_version: state.graph_version,
                smt,
                term_config,
                ranker,
                allowance,
                operation_id: None,
                pending_instances: &HashSet::new(),
                selection_counts: &self.term_selection_counts,
                artifact_capture: self.artifact_capture,
                depth: state.depth,
                refinement_step,
                profiling: profiling.clone(),
            };
            let (batch, report) = match kind {
                OperationKind::DiscoverDependencies => (
                    InstantiationBatch::default(),
                    self.quantifier
                        .discover(&mut state.binder_search, &context)?,
                ),
                OperationKind::DependencyRequest(i) => {
                    let b = self.quantifier.dependency_request(
                        &mut state.binder_search,
                        i,
                        &context,
                    )?;
                    let r = WorkReport::from_batch(&b);
                    (b, r)
                }
                _ => unreachable!(),
            };
            self.policy.effort_mut().observe(&EffortEvent::Completed {
                operation: kind,
                report: &report,
            });
            if report.selected > 0 {
                return Ok(batch);
            }
        }
    }

    #[cfg(test)]
    fn binder_candidates(
        &mut self,
        smt: &dyn crate::problem_context::ProblemContext,
        state: &mut RefinementState,
        refinement_step: u32,
        phase: crate::theories::quantifiers::SearchPhase,
        profiling: Option<Rc<RefCell<RefinementProfilingCollector>>>,
    ) -> anyhow::Result<InstantiationBatch> {
        self.quantifier.prepare_binder_search(
            smt,
            &mut state.binder_search,
            &mut state.egraph,
            &mut state.graph_version,
            &profiling,
        )?;
        let (term_config, ranker, effort) = self.policy.parts();
        self.quantifier.candidates(
            &mut state.binder_search,
            phase,
            &SearchContext::<F> {
                graph: &state.egraph,
                graph_version: state.graph_version,
                smt,
                term_config,
                ranker,
                allowance: crate::policy::effort::WorkAllowance::default(),
                operation_id: None,
                pending_instances: &HashSet::new(),
                selection_counts: &self.term_selection_counts,
                artifact_capture: self.artifact_capture,
                depth: state.depth,
                refinement_step,
                profiling,
            },
            effort,
        )
    }

    fn absorb_candidates(&mut self, state: &mut RefinementState, batch: InstantiationBatch) {
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

    fn finish_profiling_record(
        &mut self,
        profiling: Option<Rc<RefCell<RefinementProfilingCollector>>>,
    ) {
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
    use crate::policy::effort::WorkAllowance;
    use crate::policy::term_selection::array::ArrayAstSize;
    use crate::problem_context::ProblemContext;
    use crate::rule_matching::scope::CandidateScope;
    use crate::solver::SolverCheckResult;
    use crate::theories::array::array_dataflow::PropertyCone;
    use crate::theories::array::array_egraph_builder::{ArrayEGraphExpansion, FullEGraphBuilder};
    use crate::theories::quantifiers::SearchPhase;
    use crate::vmt_bmc_session::VmtBmcSession;
    use crate::{SolverBackend, YardbirdOptions};

    fn sat_fixture(input: &str) -> (Abstract<ArrayAstSize>, VmtBmcSession) {
        let commands = smt2parser::CommandStream::new(
            std::io::Cursor::new(input.as_bytes()),
            smt2parser::concrete::SyntaxBuilder,
            None,
        )
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
        let model = VMTModel::checked_from(commands).unwrap();
        let mut strategy =
            Abstract::<ArrayAstSize>::new(1, false, crate::YardbirdPolicy::new(()), false);
        let mut theory: Box<dyn ProofStrategy<'_, RefinementState>> =
            Box::new(Abstract::<ArrayAstSize>::new(
                1,
                false,
                crate::YardbirdPolicy::new(()),
                false,
            ));
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

    #[test]
    fn dependency_scheduler_discovers_paxos_initialization_chain_without_helper_ids() {
        let (mut strategy, mut smt) = sat_fixture(include_str!(
            "../../examples/distributed_protocols/paxos/paxos.encoding.vmt"
        ));
        let mut state = strategy.setup(&smt, 0).unwrap();
        let witnesses = strategy
            .binder_candidates(&smt, &mut state, 0, SearchPhase::Witnesses, None)
            .unwrap();
        assert!(witnesses.selected().next().is_some());
        strategy.absorb_candidates(&mut state, witnesses);
        strategy.finish(state, &mut smt).unwrap();
        assert_eq!(smt.check_property(), SolverCheckResult::Sat);
        let mut graph = crate::refinement_graph::RefinementGraph::new(
            strategy.quantifier.plan.signatures.clone(),
        );
        let mut prepared = strategy.quantifier.plan.prepare(&smt, &mut graph).unwrap();
        let discovery = prepared.dependency_paths(&smt).unwrap();
        let path = discovery
            .paths
            .iter()
            .find(|path| {
                !path.desired_truth
                    && path.demand.to_string().starts_with("(Read_value_Bool ")
                    && path.demand.to_string().contains("decision@0")
                    && path.requests.len() == 3
            })
            .expect("discover the three nested initial-state binders");
        assert!(path.requests.iter().all(|request| request
            .bindings
            .iter()
            .any(|(_, term)| term.to_string().contains("__yardbird_witness_"))));
        let mut state = strategy.setup(&smt, 0).unwrap();
        let profiling = Rc::new(RefCell::new(RefinementProfilingCollector::new(
            "test",
            Some(0),
            Some(1),
            vec![],
        )));
        let batch = strategy
            .dependency_candidates(&smt, &mut state, 1, Some(profiling.clone()))
            .unwrap();
        assert!(batch.selected().next().is_some());
        assert_eq!(batch.search.examined_substitutions, 0);
        assert!(batch
            .selected()
            .all(|candidate| candidate.model_violation_verified));
        assert!(Rc::try_unwrap(profiling)
            .unwrap_or_else(|_| panic!("collector still borrowed"))
            .into_inner()
            .finish()
            .counters
            .contains_key("input_binder_dependency_requests"));
    }

    #[test]
    fn dependency_scheduler_proves_a_renamed_nested_property_through_normal_driver() {
        let input = "
            (declare-sort Agent 0)
            (declare-sort Epoch 0)
            (declare-sort Payload 0)
            (declare-fun ledger () (Array Agent (Array Epoch (Array Payload Bool))))
            (define-fun init () Bool (!
                (forall ((who Agent)) (forall ((when Epoch)) (forall ((what Payload))
                    (= (select (select (select ledger who) when) what) false)))) :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! (and
                (forall ((a Agent) (b Agent) (r Epoch) (s Epoch) (v Payload) (w Payload))
                    (=> (and (select (select (select ledger a) r) v)
                             (select (select (select ledger b) s) w)) (= v w)))
                true) :invar-property 0))";
        let commands = smt2parser::CommandStream::new(
            std::io::Cursor::new(input.as_bytes()),
            smt2parser::concrete::SyntaxBuilder,
            None,
        )
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
        let model = VMTModel::checked_from(commands).unwrap();
        let mut options = YardbirdOptions::from_filename("renamed.vmt".into());
        options.profile = true;
        let mut driver = crate::Driver::new(
            model,
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler())
        .with_wall_timeout(Some(std::time::Duration::from_secs(10)));
        let result = driver
            .check_strategy(1, options.build_array_strategy())
            .unwrap();
        assert!(!result.counterexample);
        let selected: u64 = result
            .profiling
            .cost_records
            .iter()
            .map(|record| {
                record
                    .counters
                    .get("input_binder_dependency_instances_selected")
                    .copied()
                    .unwrap_or(0)
            })
            .sum();
        assert!(
            selected >= 3,
            "selected={selected}, checks={}, counters={:?}",
            result.profiling.solver_checks.len(),
            result
                .profiling
                .cost_records
                .iter()
                .map(|record| &record.counters)
                .collect::<Vec<_>>()
        );
        assert!(result.profiling.solver_checks.len() <= 8);
    }

    #[test]
    fn dependency_scheduler_uses_egg_for_remaining_variables_and_yields_to_ordinary_search() {
        let (mut strategy, smt) = sat_fixture(
            "(declare-sort Node 0)
            (declare-sort Value 0)
            (declare-fun unused () (Array Bool Bool))
            (declare-fun p (Node) Bool)
            (declare-fun q (Value) Bool)
            (define-fun init () Bool (! (forall ((x Node) (y Value))
                (and (not (p x)) (q y))) :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! (forall ((z Node)) (not (p z))) :invar-property 0))",
        );
        let mut state = strategy.setup(&smt, 0).unwrap();
        assert!(strategy
            .dependency_candidates(&smt, &mut state, 7, None)
            .unwrap()
            .candidates
            .is_empty());
        assert!(
            state.binder_search.is_none(),
            "every eighth step is reserved for ordinary refinement"
        );
        let batch = strategy
            .dependency_candidates(&smt, &mut state, 0, None)
            .unwrap();
        assert!(batch.search.examined_substitutions > 0, "egg must supply y");
        assert!(batch.selected().next().is_some());
        assert!(batch
            .selected()
            .all(|candidate| candidate.model_violation_verified));
        assert!(
            strategy
                .dependency_candidates(&smt, &mut state, 0, None)
                .unwrap()
                .candidates
                .is_empty(),
            "array-stage retries must not repeat dependency work on this model"
        );
    }

    #[test]
    fn dependency_search_reports_bounded_incompleteness_for_deep_paths() {
        let mut body = "(not (p x0 x1 x2 x3 x4 x5 x6 x7 x8))".to_string();
        for i in (0..9).rev() {
            body = format!("(forall ((x{i} Bool)) {body})");
        }
        let input = format!("(declare-fun unused () (Array Bool Bool))
            (declare-fun p (Bool Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
            (define-fun init () Bool (! {body} :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! (not (p true true true true true true true true true)) :invar-property 0))");
        let (strategy, smt) = sat_fixture(&input);
        let mut graph = crate::refinement_graph::RefinementGraph::new(
            strategy.quantifier.plan.signatures.clone(),
        );
        let mut prepared = strategy.quantifier.plan.prepare(&smt, &mut graph).unwrap();
        let discovery = prepared.dependency_paths(&smt).unwrap();
        assert!(discovery.paths.is_empty());
        assert!(discovery.budget_exhausted);
        assert!(discovery.work <= 512);
    }

    #[test]
    fn dependency_scheduler_completes_all_paxos_properties_at_depth_zero() {
        let model =
            VMTModel::from_path("examples/distributed_protocols/paxos/paxos.encoding.vmt").unwrap();
        let mut options = YardbirdOptions::from_filename("paxos.encoding.vmt".into());
        options.profile = true;
        options.cost_function = crate::CostFunction::ProtocolBmc;
        options.candidate_winners_per_group = 20;
        options.property_check_mode = PropertyCheckMode::Assumptions;
        let mut driver = crate::Driver::new(
            model,
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler())
        .with_wall_timeout(Some(std::time::Duration::from_secs(15)));
        let result = driver
            .check_strategy(1, options.build_array_strategy())
            .unwrap();
        assert_eq!(
            result
                .run_progress
                .as_ref()
                .unwrap()
                .deepest_completed_depth,
            Some(0)
        );
        assert!(!result.counterexample);
        assert!(result.profiling.cost_records.iter().any(|record| record
            .counters
            .get("input_binder_dependency_instances_selected")
            .copied()
            .unwrap_or(0)
            > 0));
        assert!(result.profiling.solver_checks.len() < 80);
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
            egraph: &mut crate::refinement_graph::RefinementGraph,
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
        strategy.profile = true;
        strategy.policy = strategy.policy.with_effort(
            crate::policy::DefaultEffort::default()
                .with_egraph_builder(Box::<DeferredFullBuilder>::default()),
        );
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
            assert!(!strategy
                .profiling_records
                .iter()
                .flat_map(|r| &r.effort)
                .any(|e| e.operation == "Binder(Expand)"));
        }
        assert!(matches!(
            strategy.sat(&mut state, &smt, 0).unwrap(),
            ProofAction::Continue
        ));
        assert!(strategy.has_pending_refinement(&state));
        assert!(strategy
            .profiling_records
            .iter()
            .flat_map(|r| &r.effort)
            .any(|e| e.operation == "Binder(Expand)"));
        assert_eq!(strategy.profiling_records.len(), 3);
        // Shared-graph growth invalidates empty passes and equality-ID caches.
        // Prepared rules and exact model evaluations still belong to this model.
        assert!(!strategy.profiling_records[1].quantifier_work.is_empty());
        assert!(!strategy.profiling_records[1]
            .counters
            .contains_key("input_binder_model_preparations"));
        assert!(state.candidates.iter().all(|candidate| {
            smt.eval_to_string(&expr_to_term(candidate.expression.clone()))
                .unwrap()
                .trim()
                == "true"
        }));
    }

    #[test]
    fn arrays_use_binder_vocabulary_before_the_full_array_stage() {
        let (mut strategy, mut smt) = expansion_fixture(true);
        let mut state = strategy.setup(&smt, 0).unwrap();
        strategy.sat(&mut state, &smt, 0).unwrap();
        assert!(strategy.has_pending_refinement(&state));
        assert!(!strategy
            .profiling_records
            .iter()
            .flat_map(|r| &r.effort)
            .any(|e| e.operation == "Binder(Expand)"));
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
    fn array_and_quantifier_refinement_cooperate_across_model_refresh() {
        let (mut strategy, mut smt) = sat_fixture(
            "(declare-fun a () (Array Bool Bool))
             (define-fun init () Bool (!
               (and (forall ((x Bool))
                      (= (select a x) (select ((as const (Array Bool Bool)) true) x)))
                    (not (select a false))) :init true))
             (define-fun trans () Bool (! true :trans true))
             (define-fun prop () Bool (! false :invar-property 0))",
        );
        let mut state = strategy.setup(&smt, 0).unwrap();
        let mut selected_categories = Vec::new();
        let mut checks = vec![SolverCheckResult::Sat];
        for step in 0..20 {
            strategy.sat(&mut state, &smt, step).unwrap();
            if !strategy.has_pending_refinement(&state) {
                continue;
            }
            selected_categories.extend(state.candidates.iter().map(|c| c.rule.category()));
            let counts = strategy.term_selection_counts.clone();
            let installed_before = smt.get_instantiations().len();
            strategy.finish(state, &mut smt).unwrap();
            assert!(smt.get_instantiations().len() > installed_before);
            let outcome = smt.check_property();
            checks.push(outcome);
            if outcome == SolverCheckResult::Unsat {
                break;
            }
            assert_eq!(outcome, SolverCheckResult::Sat);
            state = strategy.setup(&smt, 0).unwrap();
            assert!(state.binder_search.is_none());
            assert_eq!(state.egraph.number_of_classes(), 0);
            assert_eq!(strategy.term_selection_counts, counts);
        }
        // Captured from the pre-extraction binary: the binder introduces the
        // constant-array read that the array module resolves on the next model.
        assert_eq!(
            selected_categories,
            [
                crate::rule_matching::rule::QuantifiedRuleCategory::InputBinder,
                crate::rule_matching::rule::QuantifiedRuleCategory::ArrayAxiom
            ]
        );
        assert_eq!(
            checks,
            [
                SolverCheckResult::Sat,
                SolverCheckResult::Sat,
                SolverCheckResult::Unsat
            ]
        );
    }

    struct TestEffort {
        default: crate::policy::DefaultEffort,
        phase: SearchPhase,
        reverse: bool,
        done: bool,
        allowance: WorkAllowance,
        grow: bool,
        stale: bool,
        collect_two: bool,
        completed: usize,
        saved: Option<OperationId>,
    }
    impl TestEffort {
        fn phase(phase: SearchPhase) -> Self {
            Self {
                default: Default::default(),
                phase,
                reverse: false,
                done: false,
                allowance: WorkAllowance::default(),
                grow: false,
                stale: false,
                collect_two: false,
                completed: 0,
                saved: None,
            }
        }
    }
    impl crate::policy::ProofEffort for TestEffort {
        fn choose(&mut self, ctx: &EffortContext<'_>) -> EffortDecision {
            if self.stale {
                let id = *self.saved.get_or_insert_with(|| {
                    ctx.operations
                        .iter()
                        .find(|o| o.kind == OperationKind::GuardedReads)
                        .unwrap()
                        .id
                });
                return EffortDecision::Execute {
                    operation: id,
                    allowance: self.allowance,
                };
            }
            if self.completed >= 4 {
                return EffortDecision::ReturnToDriver;
            }
            if (self.done && !self.collect_two) || (self.collect_two && ctx.pending_instances >= 2)
            {
                return EffortDecision::ReturnToDriver;
            }
            let op = ctx
                .operations
                .iter()
                .find(|o| o.kind == OperationKind::Binder(self.phase))
                .unwrap();
            let mut allowance = self.allowance;
            if self.collect_two && ctx.pending_instances > 0 {
                allowance.winners = 2;
            }
            EffortDecision::Execute {
                operation: op.id,
                allowance,
            }
        }
        fn choose_binder_rule(
            &mut self,
            ctx: &crate::policy::effort::BinderEffortContext<'_>,
        ) -> Option<usize> {
            if self.reverse {
                ctx.pending_rules.last().map(|(i, _)| *i)
            } else {
                self.default.choose_binder_rule(ctx)
            }
        }
        fn observe(&mut self, event: &EffortEvent<'_>) {
            self.default.observe(event);
            match event {
                EffortEvent::BeginPass { .. } => {
                    self.done = false;
                    self.completed = 0;
                }
                EffortEvent::Completed { .. } => {
                    self.done = true;
                    self.completed += 1;
                    if self.grow {
                        self.allowance.binder_search_limit += 1;
                        self.allowance.winners += 1;
                    }
                }
                _ => {}
            }
        }
        fn egraph_builder(&self) -> Box<dyn ArrayEGraphBuilder> {
            self.default.egraph_builder()
        }
        fn requires_property_cone(&self) -> bool {
            self.default.requires_property_cone()
        }
    }

    #[test]
    fn effort_can_expand_binders_before_any_array_stage() {
        let (mut strategy, smt) = expansion_fixture(false);
        strategy.policy = strategy
            .policy
            .with_effort(TestEffort::phase(SearchPhase::Expand));
        let mut state = strategy.setup(&smt, 0).unwrap();
        strategy.sat(&mut state, &smt, 0).unwrap();
        assert!(strategy.has_pending_refinement(&state));
        assert!(state.array_expansion.is_none());
        assert!(state.egraph.number_of_classes() > 0);
    }

    #[test]
    fn effort_owns_rule_order_without_engine_fairness_override() {
        let (mut strategy, mut smt) = round_robin_fixture();
        let expected = format!(
            "input-binder-{}",
            strategy.quantifier.plan.rules.last().unwrap().name
        );
        let mut effort = TestEffort::phase(SearchPhase::Conflicts);
        effort.reverse = true;
        strategy.policy = strategy.policy.with_effort(effort);
        for step in 0..3 {
            assert_eq!(smt.check_property(), SolverCheckResult::Sat);
            let mut state = strategy.setup(&smt, 0).unwrap();
            strategy.sat(&mut state, &smt, step).unwrap();
            assert_eq!(state.candidates.len(), 1);
            assert_eq!(state.candidates[0].rule.name(), expected);
        }
    }

    #[test]
    fn shared_graph_growth_restarts_search_but_keeps_model_evaluations() {
        let (mut strategy, smt) = expansion_fixture(false);
        strategy.policy = strategy
            .policy
            .with_effort(TestEffort::phase(SearchPhase::Conflicts));
        let mut state = strategy.setup(&smt, 0).unwrap();
        strategy.sat(&mut state, &smt, 0).unwrap();
        let snapshot = state
            .egraph
            .classes()
            .map(|c| (c.id, c.nodes.clone()))
            .collect::<Vec<_>>();
        let version = state.graph_version;
        strategy.sat(&mut state, &smt, 0).unwrap();
        assert_eq!(version, state.graph_version);
        assert_eq!(
            snapshot,
            state
                .egraph
                .classes()
                .map(|c| (c.id, c.nodes.clone()))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            strategy.profiling_records[1].counters["input_binder_empty_passes_reused"],
            1
        );

        state
            .egraph
            .admit(&smt, &"(or (and true true) false)".parse().unwrap(), true)
            .unwrap();
        state.egraph.rebuild();
        state.graph_version += 1;
        strategy.sat(&mut state, &smt, 0).unwrap();
        let record = &strategy.profiling_records[2];
        assert!(record.rule_instantiation.rule_search_calls > 0);
        assert!(!record
            .counters
            .contains_key("input_binder_empty_passes_reused"));
        assert!(!record
            .counters
            .contains_key("input_binder_model_preparations"));
        assert_eq!(
            record
                .counters
                .get("input_binder_obligation_cache_hits")
                .copied()
                .unwrap_or(0),
            0
        );
        assert!(record
            .quantifier_work
            .values()
            .flat_map(|phases| phases.values())
            .any(|phase| phase
                .counters
                .get("evaluation_cache_hits")
                .copied()
                .unwrap_or(0)
                > 0));
    }

    #[test]
    fn changed_effort_allowance_reconsiders_empty_pass_but_reuses_model() {
        let (mut strategy, smt) = expansion_fixture(false);
        strategy.profile = true;
        let mut effort = TestEffort::phase(SearchPhase::Conflicts);
        effort.allowance.binder_page_size = 1;
        effort.allowance.binder_search_limit = 1;
        effort.grow = true;
        strategy.policy = strategy.policy.with_effort(effort);
        let mut state = strategy.setup(&smt, 0).unwrap();
        strategy.sat(&mut state, &smt, 0).unwrap();
        strategy.sat(&mut state, &smt, 0).unwrap();
        assert_eq!(strategy.profiling_records.len(), 2);
        for r in &strategy.profiling_records {
            assert!(r.rule_instantiation.rule_search_calls > 0);
        }
        let second = &strategy.profiling_records[1];
        assert!(!second
            .counters
            .contains_key("input_binder_empty_passes_reused"));
        assert!(!second
            .counters
            .contains_key("input_binder_model_preparations"));
        assert!(
            second
                .counters
                .get("input_binder_obligation_cache_hits")
                .copied()
                .unwrap_or(0)
                > 0
        );
    }

    #[test]
    fn effort_can_collect_multiple_batches_before_installation() {
        let (mut strategy, mut smt) = round_robin_fixture();
        let mut effort = TestEffort::phase(SearchPhase::Conflicts);
        effort.collect_two = true;
        effort.reverse = true;
        strategy.policy = strategy.policy.with_effort(effort);
        let mut state = strategy.setup(&smt, 0).unwrap();
        strategy.sat(&mut state, &smt, 0).unwrap();
        assert_eq!(state.candidates.len(), 2);
        assert_eq!(
            state.candidates[0].rule.name(),
            state.candidates[1].rule.name()
        );
        assert_ne!(
            state.candidates[0].expression,
            state.candidates[1].expression
        );
        let before = smt.get_instantiations().len();
        strategy.finish(state, &mut smt).unwrap();
        assert_eq!(smt.get_instantiations().len(), before + 2);
    }

    #[test]
    fn dependency_discovery_respects_small_total_allowance() {
        let (strategy, smt) = round_robin_fixture();
        let mut graph = crate::refinement_graph::RefinementGraph::new(
            strategy.quantifier.plan.signatures.clone(),
        );
        let mut prepared = strategy.quantifier.plan.prepare(&smt, &mut graph).unwrap();
        let full = prepared
            .dependency_paths_with_allowance(&smt, &WorkAllowance::default())
            .unwrap();
        assert!(full.work > 1);
        for limit in [1, 2, 3] {
            let allowance = WorkAllowance {
                dependency_work: limit,
                ..WorkAllowance::default()
            };
            allowance.validate().unwrap();
            let report = prepared
                .dependency_paths_with_allowance(&smt, &allowance)
                .unwrap();
            assert!(report.work <= limit);
            if full.work > limit {
                assert!(report.budget_exhausted);
            }
        }
    }

    #[test]
    fn invalid_effort_allowance_is_rejected_before_matching() {
        let (mut strategy, smt) = round_robin_fixture();
        let mut effort = TestEffort::phase(SearchPhase::Conflicts);
        effort.allowance.winners = 0;
        strategy.policy = strategy.policy.with_effort(effort);
        let mut state = strategy.setup(&smt, 0).unwrap();
        let error = strategy
            .sat(&mut state, &smt, 0)
            .err()
            .expect("invalid allowance");
        assert!(error.to_string().contains("candidate groups need a winner"));
        assert!(state.binder_search.is_none());
    }

    #[test]
    fn stale_effort_operation_is_rejected_before_execution() {
        let (mut strategy, smt) = round_robin_fixture();
        let mut effort = TestEffort::phase(SearchPhase::Conflicts);
        effort.stale = true;
        strategy.policy = strategy.policy.with_effort(effort);
        let mut state = strategy.setup(&smt, 0).unwrap();
        let error = strategy
            .sat(&mut state, &smt, 0)
            .err()
            .expect("reject stale operation");
        assert!(error.to_string().contains("stale or unavailable operation"));
        assert!(state.candidates.is_empty());
        assert!(state.binder_search.is_none());
    }

    #[test]
    fn exhausted_search_widens_then_grows_on_the_same_model() {
        let (mut strategy, smt) = sat_fixture(
            "(declare-fun a () (Array Bool Bool))
             (define-fun init () Bool (! true :init true))
             (define-fun trans () Bool (! true :trans true))
             (define-fun prop () Bool (! false :invar-property 0))",
        );
        strategy.profile = true;
        strategy.policy = strategy.policy.with_effort(
            crate::policy::DefaultEffort::default()
                .with_egraph_builder(Box::<DeferredFullBuilder>::default()),
        );
        strategy.profile = true;
        let mut state = strategy.setup(&smt, 0).unwrap();
        for _ in 0..2 {
            strategy.sat(&mut state, &smt, 0).unwrap();
            assert!(!strategy.has_pending_refinement(&state));
        }
        strategy.sat(&mut state, &smt, 0).unwrap();
        let version = state.graph_version;
        strategy.sat(&mut state, &smt, 0).unwrap();
        let widened = &strategy.profiling_records[3].effort;
        assert!(widened
            .iter()
            .any(|e| e.allowance.is_some_and(|a| a.winners == 2)));
        strategy.sat(&mut state, &smt, 0).unwrap();
        assert!(state.graph_version > version);
        let growth = strategy.profiling_records[4]
            .effort
            .iter()
            .find(|e| e.operation == "GrowVocabulary")
            .unwrap();
        assert!(growth.report.terms_added > 0);
        assert!(growth.report.vocabulary_work <= growth.allowance.unwrap().vocabulary_work);
        assert!(!strategy.has_pending_refinement(&state));
    }

    #[test]
    fn default_effort_recovers_array_matches_hidden_by_small_caps() {
        let (mut strategy, smt) = sat_fixture(
            "(declare-fun a () (Array Int Int))
             (define-fun init () Bool (! (and
               (not (= (select (store a 0 10) 0) 10))
               (not (= (select (store a 1 11) 1) 11))
               (not (= (select (store a 2 12) 2) 12))) :init true))
             (define-fun trans () Bool (! true :trans true))
             (define-fun prop () Bool (! false :invar-property 0))",
        );
        strategy.profile = true;
        strategy.policy =
            strategy
                .policy
                .with_effort(crate::policy::DefaultEffort::default().with_allowance(
                    WorkAllowance {
                        array_initial_limit: 1,
                        array_rounds: 1,
                        vocabulary_work: 1,
                        ..Default::default()
                    },
                ));
        let mut state = strategy.setup(&smt, 0).unwrap();
        let model = state.model_version;
        for _ in 0..12 {
            strategy.sat(&mut state, &smt, 0).unwrap();
            if strategy.has_pending_refinement(&state) {
                break;
            }
        }
        assert_eq!(state.model_version, model);
        assert!(
            strategy.has_pending_refinement(&state),
            "wider caps must recover the skipped array rule"
        );
        let records = strategy
            .profiling_records
            .iter()
            .flat_map(|p| &p.effort)
            .collect::<Vec<_>>();
        assert!(records
            .iter()
            .any(|e| e.operation == "ArrayCandidates" && e.report.budget_exhausted));
        assert!(records.iter().any(|e| e.operation == "ArrayCandidates"
            && e.allowance.is_some_and(|a| a.array_initial_limit > 1)
            && e.report.selected > 0));
    }

    #[test]
    fn vocabulary_growth_is_bounded_typed_and_deterministic() {
        let (mut strategy, smt) = sat_fixture(
            "(declare-fun a () (Array Int Int))
             (declare-fun f (Int) Int)
             (declare-fun p (Int) Bool)
             (define-fun init () Bool (! true :init true))
             (define-fun trans () Bool (! true :trans true))
             (define-fun prop () Bool (! false :invar-property 0))",
        );
        let build = |graph: &mut crate::refinement_graph::RefinementGraph| {
            graph.admit(&smt, &"0".parse().unwrap(), true).unwrap();
            for _ in 0..16 {
                let growth = graph.grow_vocabulary(&smt, 2).unwrap();
                assert!(growth.examined <= 2);
                assert!(growth.added <= growth.examined);
            }
            graph
                .terms
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
        };
        let mut first = strategy.setup(&smt, 0).unwrap();
        let mut second = strategy.setup(&smt, 0).unwrap();
        let terms = build(&mut first.egraph);
        assert_eq!(terms, build(&mut second.egraph));
        for term in ["(f 0)", "(p 0)", "(+ 0 1)", "(- 0 1)"] {
            let expression = crate::terms::language::translate_term(term.parse().unwrap()).unwrap();
            assert!(first.egraph.lookup_expr(&expression).is_some(), "{term}");
        }
        assert!(terms.iter().all(|term| !term.contains("!val!")));
        assert!(
            smt.get_instantiations().is_empty(),
            "vocabulary is not asserted"
        );
    }

    #[test]
    fn vocabulary_revisit_versions_new_model_equalities_even_without_new_roots() {
        let (mut strategy, smt) = sat_fixture(
            "(declare-fun a () (Array Int Int))
             (declare-fun A (Int) Bool)
             (define-fun init () Bool (! (A 0) :init true))
             (define-fun trans () Bool (! true :trans true))
             (define-fun prop () Bool (! false :invar-property 0))",
        );
        let mut state = strategy.setup(&smt, 0).unwrap();
        for term in ["0", "(A 0)"] {
            state
                .egraph
                .admit(&smt, &term.parse().unwrap(), false)
                .unwrap();
        }
        state.egraph.rebuild();
        let version = state.graph_version;
        assert!(state.egraph.lookup_expr(&"true".parse().unwrap()).is_none());
        let report = state.grow_vocabulary(&smt, 1).unwrap();
        assert_eq!(report.terms_added, 0);
        assert_eq!(report.vocabulary_work, 1);
        assert!(state.graph_version > version);
        let expression = crate::terms::language::translate_term("(A 0)".parse().unwrap()).unwrap();
        assert_eq!(
            state
                .egraph
                .find(state.egraph.lookup_expr(&expression).unwrap()),
            state
                .egraph
                .find(state.egraph.lookup_expr(&"true".parse().unwrap()).unwrap())
        );
    }

    fn profiled_binder_pass(
        strategy: &mut Abstract<ArrayAstSize>,
        state: &mut RefinementState,
        smt: &VmtBmcSession,
        phase: SearchPhase,
        step: u32,
    ) -> ProfilingRecord {
        let profiling = Rc::new(RefCell::new(RefinementProfilingCollector::new(
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
                .quantifier
                .plan
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
            .quantifier
            .plan
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
