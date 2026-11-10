//! Input-binder compilation and search. Policy-owned rotation survives solver checks;
//! prepared matches and empty-pass caches belong to one model in coordinator state.
use crate::instance_installation::assertion_tracker::canonical_instantiation_key;
use crate::policy::term_selection::TermCostFactory;
use crate::profiling::RefinementProfilingCollector;
use crate::rule_matching::candidate::InstantiationBatch;
use crate::rule_matching::candidate_builder::{InstantiationInstrumentation, InstantiationOptions};
use crate::rule_matching::search_context::SearchContext;
use log::info;
use rustc_hash::FxHashMap;
use smt2parser::vmt::VMTModel;
use std::{cell::RefCell, collections::HashMap, rc::Rc, time::Instant};

#[derive(Default)]
pub(crate) struct QuantifierRefinement {
    pub(crate) plan: crate::theories::quantifiers::QuantifierPlan,
    pub(crate) provenance: crate::theories::quantifiers::provenance::QuantifierProvenance,
    pub(crate) configuration_error: Option<String>,
    pub(crate) owns_quantifiers: bool,
    pub(crate) property_witnesses: Vec<smt2parser::concrete::Symbol>,
    pub(crate) exact_grounding: bool,
    pub(crate) source_captures: bool,
    pub(crate) read_frontiers: bool,
}

/// One solver model's compiled searches and graph-versioned unsuccessful passes.
pub(crate) struct BinderSearchState {
    prepared: crate::theories::quantifiers::PreparedQuantifierSearch,
    empty_passes: HashMap<crate::theories::quantifiers::SearchPhase, BinderPassContext>,
    pub(crate) requests: Vec<DependencyWork>,
    pub(crate) dependencies_searched: bool,
    traced: Option<super::countermodel_requests::TracedEquationSearch>,
    traced_attempted: std::collections::HashSet<usize>,
    demanded_indices: super::demanded_indices::DemandedIndices,
    // Source tuples and their attempted work belong to this solver model.
    exact_work: HashMap<super::BinderSearchRequest, usize>,
    ground_terms: Option<super::ground::GroundTerms>,
}

pub(crate) struct DependencyWork {
    pub(crate) request: crate::theories::quantifiers::BinderSearchRequest,
    pub(crate) description: String,
    pub(super) origin: Option<crate::rule_matching::provenance::CountermodelOrigin>,
}

struct BinderPassContext {
    graph_version: u64,
    refinement_step: u32,
    selection_counts: FxHashMap<String, u32>,
    allowance: crate::policy::effort::WorkAllowance,
    budget_exhausted_rules: Vec<String>,
    pending_instances: std::collections::HashSet<smt2parser::concrete::Term>,
}

impl QuantifierRefinement {
    #[cfg(test)]
    pub(crate) fn configure_model(&mut self, model: VMTModel, profile: bool) -> VMTModel {
        self.configure(model, profile, false, true)
    }

    pub(super) fn configure_eager_model(&mut self, model: VMTModel) -> VMTModel {
        self.configure(model, false, true, true)
    }

    pub(crate) fn configure_with_arrays(
        &mut self,
        model: VMTModel,
        profile: bool,
        abstract_arrays: bool,
    ) -> VMTModel {
        self.configure(model, profile, false, abstract_arrays)
    }

    fn configure(
        &mut self,
        model: VMTModel,
        profile: bool,
        retain_native: bool,
        abstract_arrays: bool,
    ) -> VMTModel {
        self.configuration_error = None;
        self.owns_quantifiers = model.as_commands().iter().any(|command| match command {
            smt2parser::concrete::Command::DefineFun { term, .. }
            | smt2parser::concrete::Command::Assert { term } => {
                crate::theories::quantifiers::contains_binders(term)
            }
            _ => false,
        });
        let model =
            match crate::theories::quantifiers::provenance::scope_model(model.clone(), profile) {
                Ok((model, provenance)) => {
                    self.provenance = provenance;
                    model
                }
                Err(error) => {
                    self.configuration_error = Some(error.to_string());
                    return model;
                }
            };
        let (model, bindings) = model.herbrandize_universal_property_with_bindings();
        self.property_witnesses = bindings
            .iter()
            .map(|(_, witness)| witness.clone())
            .collect();
        self.provenance.record_property_witnesses(&bindings);
        let herbrand_witnesses = bindings.len();
        if herbrand_witnesses > 0 {
            info!("Herbrandized universal property with {herbrand_witnesses} witness constants");
        }
        let original = model.clone();
        let lowered = if !abstract_arrays {
            super::lowering::lower_model_with_arrays(
                model,
                &mut self.provenance,
                retain_native,
                false,
            )
        } else if retain_native {
            super::lowering::lower_model_for_eager(model, &mut self.provenance, true)
        } else {
            super::lower_model_with_provenance(model, &mut self.provenance)
        };
        match lowered {
            Ok((model, plan)) => {
                info!(
                    "Abstracted {} quantifier/lambda expressions for Yardbird instantiation",
                    plan.rules.len()
                );
                self.plan = plan;
                model
            }
            Err(error) => {
                self.configuration_error = Some(error.to_string());
                original
            }
        }
    }

    pub(crate) fn prepare_binder_search(
        &self,
        smt: &dyn crate::problem_context::ProblemContext,
        state: &mut Option<BinderSearchState>,
        graph: &mut crate::refinement_graph::RefinementGraph,
        graph_version: &mut u64,
        profiling: &Option<Rc<RefCell<RefinementProfilingCollector>>>,
    ) -> anyhow::Result<()> {
        if state.is_none() {
            let start = Instant::now();
            let mut prepared = self.plan.prepare(smt, graph)?;
            if self.source_captures {
                prepared.source_captures = Some(super::source_captures::SourceCaptures::new(
                    &self.plan,
                    smt.get_source_subterms(),
                    &smt.get_array_types(),
                ));
            }
            *graph_version += 1;
            *state = Some(BinderSearchState {
                prepared,
                empty_passes: HashMap::new(),
                dependencies_searched: false,
                requests: Vec::new(),
                traced: None,
                traced_attempted: Default::default(),
                demanded_indices: Default::default(),
                exact_work: HashMap::new(),
                ground_terms: None,
            });
            if let Some(profiling) = profiling {
                let mut profiling = profiling.borrow_mut();
                profiling.record_timing("input_binder_prepare", start.elapsed());
                profiling.add_counter("input_binder_model_preparations", 1);
            }
        }
        let search = state.as_mut().unwrap();
        if search.prepared.graph_version() != *graph_version {
            search.prepared.refresh_graph(graph, *graph_version);
            search.empty_passes.clear();
            // Symbolic requests keep their indices and exact bindings within
            // this model; only their prepared match cursors need refreshing.
            search.dependencies_searched = false;
        }
        Ok(())
    }

    pub(crate) fn discover_obligations<F: TermCostFactory + 'static>(
        &self,
        state: &mut Option<BinderSearchState>,
        obligations: &mut crate::refinement_obligations::RefinementObligations,
        trace: Option<&crate::countermodel::CountermodelTrace>,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<(crate::policy::effort::WorkReport, InstantiationBatch)> {
        if self.read_frontiers {
            return self.discover_read_frontiers(state, obligations, trace, context);
        }
        // A frontier supplements ordinary discovery within its policy budget.
        // It must not replace the action/order/initializer work already queued.
        let (mut report, batch) =
            self.discover_ordinary_obligations(state, obligations, context)?;
        if report.selected > 0 {
            return Ok((report, batch));
        }
        let search = state.as_mut().unwrap();
        if search.traced.is_none() {
            if let Some(trace) = trace.filter(|trace| trace.model_version == context.model_version)
            {
                search.traced = Some(super::countermodel_requests::TracedEquationSearch::new(
                    trace,
                    &self.plan,
                    context.smt,
                ));
            }
        }
        if let Some(traced) = &mut search.traced {
            let remaining = context
                .allowance
                .dependency_work
                .saturating_sub(report.dependency_work);
            report.dependency_work += traced.advance(&self.plan, remaining, &mut search.requests);
            report.continuable |= traced.pending();
            report.budget_exhausted |= traced.pending();
            search.dependencies_searched = !report.continuable;
        }
        Ok((report, batch))
    }

    /// Execute demanded tuples before ordinary candidates can consume this
    /// model's batch. The existing DiscoverDependencies operation still owns
    /// both producers, including its supplement scheduling and total budgets.
    fn discover_read_frontiers<F: TermCostFactory + 'static>(
        &self,
        state: &mut Option<BinderSearchState>,
        obligations: &mut crate::refinement_obligations::RefinementObligations,
        trace: Option<&crate::countermodel::CountermodelTrace>,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<(crate::policy::effort::WorkReport, InstantiationBatch)> {
        let (reserved_work, reserved_page) = context.allowance.read_frontier_reservation();
        let search = state.as_mut().unwrap();
        if search.traced.is_none() {
            if let Some(trace) = trace.filter(|t| t.model_version == context.model_version) {
                search.demanded_indices =
                    super::demanded_indices::DemandedIndices::new(trace, &self.plan);
                search.traced = Some(super::countermodel_requests::TracedEquationSearch::new(
                    trace,
                    &self.plan,
                    context.smt,
                ));
            }
        }
        let before = search
            .requests
            .iter()
            .filter(|r| r.origin.is_some())
            .count();
        let work = search.traced.as_mut().map_or(0, |traced| {
            traced.advance(&self.plan, reserved_work, &mut search.requests)
        });
        let pending = search.traced.as_ref().is_some_and(|t| t.pending());
        let after = search
            .requests
            .iter()
            .filter(|r| r.origin.is_some())
            .count();
        if let Some(profile) = &context.profiling {
            let mut p = profile.borrow_mut();
            p.add_counter("traced_frontier_reserved_work", reserved_work as u64);
            p.add_counter("traced_frontier_work", work as u64);
            p.add_counter(
                "traced_frontier_requests_discovered",
                (after - before) as u64,
            );
        }
        // Stable indices refer to symbolic, model-local requests. A page that
        // finds nothing cannot monopolize later slices; ordinary search still
        // offers these same requests through its normal fallback schedule.
        let requests = search
            .requests
            .iter()
            .enumerate()
            .filter(|(i, r)| r.origin.is_some() && !search.traced_attempted.contains(i))
            .map(|(i, _)| i)
            .take(4.min(reserved_page))
            .collect::<Vec<_>>();
        let page = reserved_page / requests.len().max(1);
        let mut charged_page = 0;
        let mut examined = 0;
        let mut returned = 0;
        for index in requests {
            state.as_mut().unwrap().traced_attempted.insert(index);
            let mut allowance = context.allowance;
            allowance.dependency_work = 0; // no second discovery budget
            allowance.binder_page_size = page;
            allowance.binder_search_limit = allowance.binder_search_limit.min(page);
            let batch =
                self.dependency_request(state, index, &context.with_allowance(allowance))?;
            charged_page += page;
            examined += batch.search.examined_substitutions;
            returned += batch.search.returned_substitutions;
            let mut report = crate::policy::effort::WorkReport::from_batch(&batch);
            if let Some(profile) = &context.profiling {
                let mut p = profile.borrow_mut();
                p.add_counter("traced_frontier_requests_attempted", 1);
                p.add_counter("traced_frontier_instances_selected", report.selected as u64);
            }
            if report.selected > 0 {
                report.dependency_work = work;
                report.examined_substitutions = examined;
                report.returned_substitutions = returned;
                report.continuable |= pending;
                report.budget_exhausted |= pending;
                return Ok((report, batch));
            }
        }
        let mut allowance = context.allowance;
        allowance.dependency_work -= work; // return unused reservation
        allowance.binder_page_size -= charged_page;
        let (mut report, batch) = self.discover_ordinary_obligations(
            state,
            obligations,
            &context.with_allowance(allowance),
        )?;
        if let Some(profile) = &context.profiling {
            profile.borrow_mut().add_counter(
                "traced_frontier_ordinary_work",
                report.dependency_work as u64,
            );
        }
        report.dependency_work += work;
        report.examined_substitutions += examined;
        report.returned_substitutions += returned;
        report.continuable |= pending;
        report.budget_exhausted |= pending;
        state.as_mut().unwrap().dependencies_searched = !report.continuable;
        Ok((report, batch))
    }

    fn discover_ordinary_obligations<F: TermCostFactory + 'static>(
        &self,
        state: &mut Option<BinderSearchState>,
        obligations: &mut crate::refinement_obligations::RefinementObligations,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<(crate::policy::effort::WorkReport, InstantiationBatch)> {
        // Structural transport follows explicit stores. Lambda-defined arrays
        // need their equation matcher; do not steer those models with an
        // incomplete structural explanation. SMTLIB/actionless inputs likewise
        // retain their existing dependency search.
        if context
            .formulas
            .index
            .is_none_or(|index| index.actions().is_empty())
            || self
                .plan
                .rules
                .iter()
                .any(|rule| rule.kind == super::BinderKind::Lambda)
        {
            // Directed initializer instances remain usable even when structural
            // dependency transport is unavailable for this encoding.
            let batch = obligations.candidates(context)?;
            let mut report = crate::policy::effort::WorkReport::from_batch(&batch);
            let fallback = self.discover(state, context)?;
            report.dependency_work = fallback.dependency_work;
            report.budget_exhausted = fallback.budget_exhausted;
            // The binder search itself may still have paged work; losing this
            // would let the effort scheduler treat it as exhausted early.
            report.continuable = fallback.continuable;
            return Ok((report, batch));
        }
        let discovery = obligations.discover(
            context.formulas,
            context.smt,
            context.depth,
            context.model_version,
            &context.allowance,
        )?;
        let batch = obligations.candidates(context)?;
        let mut report = crate::policy::effort::WorkReport::from_batch(&batch);
        report.dependency_work = discovery.work;
        report.continuable = discovery.pending > 0;
        report.budget_exhausted = report.continuable;
        if let Some(profile) = &context.profiling {
            let mut p = profile.borrow_mut();
            p.add_counter("obligation_demands", discovery.demands as u64);
            p.add_counter("obligation_pending_work", discovery.pending as u64);
            p.add_counter("obligation_search_contexts", discovery.contexts as u64);
        }
        if report.selected == 0 && !report.continuable {
            let mut allowance = context.allowance;
            if self.read_frontiers {
                allowance.dependency_work = allowance
                    .dependency_work
                    .saturating_sub(report.dependency_work);
            }
            let fallback = self.discover(state, &context.with_allowance(allowance))?;
            report.dependency_work += fallback.dependency_work;
            report.budget_exhausted |= fallback.budget_exhausted;
        } else {
            state.as_mut().unwrap().dependencies_searched = !report.continuable;
        }
        Ok((report, batch))
    }

    pub(crate) fn discover<F: TermCostFactory + 'static>(
        &self,
        state: &mut Option<BinderSearchState>,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<crate::policy::effort::WorkReport> {
        let search = state.as_mut().unwrap();
        let _phase_guard = context.profiling.as_ref().map(|p| {
            crate::profiling::QuantifierPhaseGuard::new(p.clone(), "input_binder_dependencies")
        });
        let start = Instant::now();
        let discovery = search
            .prepared
            .dependency_paths_with_allowance(context.smt, &context.allowance)?;
        if let Some(profiling) = &context.profiling {
            let mut p = profiling.borrow_mut();
            p.record_timing("input_binder_dependency_discovery", start.elapsed());
            p.add_counter("input_binder_dependency_demands", discovery.demands as u64);
            p.add_counter("input_binder_dependency_work", discovery.work as u64);
            p.add_counter(
                "input_binder_dependency_paths",
                discovery.paths.len() as u64,
            );
            p.add_counter(
                "input_binder_dependency_budget_exhausted",
                u64::from(discovery.budget_exhausted),
            );
        }
        let mut seen = search
            .requests
            .iter()
            .map(|work| work.request.clone())
            .collect::<std::collections::HashSet<_>>();
        for path in discovery.paths {
            let route = path
                .requests
                .iter()
                .map(|r| r.helper.clone())
                .collect::<Vec<_>>()
                .join(" -> ");
            for request in path.requests {
                if seen.insert(request.clone()) {
                    let description = format!(
                        "{}={} via {route}: {} {:?} {:?}",
                        path.demand,
                        path.desired_truth,
                        request.helper,
                        request.phase,
                        request.bindings
                    );
                    search.requests.push(DependencyWork {
                        request,
                        description,
                        origin: None,
                    });
                }
            }
        }
        search.dependencies_searched = true;
        Ok(crate::policy::effort::WorkReport {
            dependency_work: discovery.work,
            budget_exhausted: discovery.budget_exhausted,
            ..Default::default()
        })
    }

    /// A preference within the rule/phase already chosen by effort. Literal
    /// demanded indices survive extraction, while captures and other variables
    /// still use ordinary matching. Failed attempts leave half the page free.
    fn scheduled_indices<F: TermCostFactory + 'static>(
        &self,
        prepared: &mut super::PreparedQuantifierSearch,
        indices: &mut super::demanded_indices::DemandedIndices,
        helper: &str,
        phase: super::SearchPhase,
        context: &SearchContext<'_, F>,
        known: &std::collections::HashSet<smt2parser::concrete::Term>,
    ) -> anyhow::Result<(Option<InstantiationBatch>, usize, usize, usize)> {
        if !self.read_frontiers || phase == super::SearchPhase::Witnesses {
            return Ok((None, 0, 0, 0));
        }
        let reserved = context.allowance.binder_page_size / 2;
        let requests = indices.requests(&self.plan, helper, phase, 4.min(reserved / 2));
        let allocation = reserved / requests.len().max(1);
        let mut charged = 0;
        let mut examined = 0;
        let mut returned = 0;
        for request in requests {
            indices.mark_attempted(&request);
            let mut allowance = context.allowance;
            // The regular matcher includes one lookahead in its work count.
            allowance.binder_page_size = allocation - 1;
            allowance.binder_search_limit = allowance.binder_search_limit.min(allocation - 1);
            let mut batch = prepared.candidates(
                context.graph,
                |term| context.smt.eval_to_string(term),
                super::BinderSearch::RequestPage(&request, allowance),
                |cost_context| context.term_cost(cost_context, context.depth as u32),
                InstantiationOptions {
                    search_allowance: allowance,
                    additional_terms: vec![],
                    candidate_catalog: prepared.catalog.clone(),
                    candidate_scope: crate::rule_matching::scope::CandidateScope::AllCandidates,
                    refinement_step: context.refinement_step,
                    selection_counts: context.selection_counts.clone(),
                    depth: context.depth,
                    instrumentation: InstantiationInstrumentation {
                        artifact_capture: context.artifact_capture,
                        profiling: context.profiling.clone(),
                    },
                },
            )?;
            charged += allocation;
            examined += batch.search.examined_substitutions;
            returned += batch.search.returned_substitutions;
            let summary = self.select_scheduled(&mut batch, None, known, context)?;
            if let Some(profile) = &context.profiling {
                let mut p = profile.borrow_mut();
                p.add_counter("demanded_index_requests_attempted", 1);
                p.add_counter(
                    "demanded_index_instances_selected",
                    summary.selected_binders as u64,
                );
                p.add_counter(
                    "demanded_index_work",
                    batch.search.examined_substitutions as u64,
                );
            }
            if batch.selected().next().is_some() {
                // Caller accounts for all prefix attempts, including this batch.
                batch.search.examined_substitutions = 0;
                batch.search.returned_substitutions = 0;
                return Ok((Some(batch), charged, examined, returned));
            }
        }
        Ok((None, charged, examined, returned))
    }

    /// Exact search runs only after the policy chose a helper/phase/request.
    /// Reserve at most a quarter of its page for it, charging those attempts
    /// against both the current page and the rule's total search allowance.
    fn scheduled_exact<F: TermCostFactory>(
        &self,
        attempted: &mut HashMap<super::BinderSearchRequest, usize>,
        terms: &mut Option<super::ground::GroundTerms>,
        request: &super::BinderSearchRequest,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<(
        Option<InstantiationBatch>,
        crate::policy::effort::WorkAllowance,
    )> {
        let mut allowance = context.allowance;
        if !self.exact_grounding {
            return Ok((None, allowance));
        }
        let mut result = None;
        if !attempted.contains_key(request) {
            let limit = (allowance.binder_page_size / 4)
                .min(allowance.binder_search_limit / 4)
                .min(allowance.dependency_work);
            let start = Instant::now();
            let (report, batch) = if limit > 0 {
                super::ground::GroundBinders::for_request(&self.plan, request.clone())?
                    .candidates_indexed(
                        context,
                        limit,
                        terms.get_or_insert_with(|| {
                            super::ground::GroundTerms::new(context.smt.get_all_subterms())
                        }),
                    )?
            } else {
                (Default::default(), InstantiationBatch::default())
            };
            attempted.insert(request.clone(), report.examined_substitutions);
            allowance.binder_page_size -= report.examined_substitutions;
            if let Some(profile) = &context.profiling {
                let mut p = profile.borrow_mut();
                p.record_timing("input_binder_scheduled_exact", start.elapsed());
                p.add_counter("input_binder_scheduled_exact_attempts", 1);
                p.add_counter(
                    "input_binder_scheduled_exact_work",
                    report.examined_substitutions as u64,
                );
                p.add_counter(
                    "input_binder_scheduled_exact_candidates",
                    report.selected as u64,
                );
                p.add_counter(
                    "input_binder_scheduled_exact_fallbacks",
                    u64::from(report.selected == 0),
                );
            }
            if report.selected > 0 {
                result = Some(batch);
            }
        }
        allowance.binder_search_limit = allowance
            .binder_search_limit
            .saturating_sub(attempted[request])
            .max(1);
        Ok((result, allowance))
    }

    /// Exact tuples supplement an unproductive page; they must not preempt
    /// the policy's validated ordinary grounding choices (including witnesses).
    /// Keep the ordinary continuation report even when exact tuples are used.
    fn select_scheduled<F: TermCostFactory>(
        &self,
        batch: &mut InstantiationBatch,
        exact: Option<InstantiationBatch>,
        known: &std::collections::HashSet<smt2parser::concrete::Term>,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<crate::rule_matching::candidate::BatchSummary> {
        let scope = crate::rule_matching::scope::CandidateScope::AllCandidates;
        let prepare = |batch: &mut InstantiationBatch| {
            batch.prepare_with_ranker(
                scope,
                known,
                context.allowance.winners,
                context.ranker,
                |term| context.smt.eval_to_string(term),
                |c| context.installable_expression(&c.expression),
            )
        };
        let had_exact = exact.is_some();
        let (summary, used_exact) = select_ordinary_then_exact(batch, exact, prepare)?;
        if let Some(profile) = &context.profiling {
            if used_exact {
                profile.borrow_mut().add_counter(
                    "input_binder_scheduled_exact_selected",
                    summary.selected_binders as u64,
                );
            } else if had_exact {
                profile
                    .borrow_mut()
                    .add_counter("input_binder_scheduled_ordinary_preferred", 1);
            }
        }
        Ok(summary)
    }

    pub(crate) fn dependency_request<F: TermCostFactory + 'static>(
        &self,
        state: &mut Option<BinderSearchState>,
        index: usize,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<InstantiationBatch> {
        let search = state
            .as_mut()
            .ok_or_else(|| anyhow::anyhow!("dependency search not prepared"))?;
        let request = search
            .requests
            .get(index)
            .ok_or_else(|| anyhow::anyhow!("unknown dependency request"))?;
        let origin = request.origin.clone();
        let request = &request.request;
        let (exact, page_allowance) = self.scheduled_exact(
            &mut search.exact_work,
            &mut search.ground_terms,
            request,
            context,
        )?;
        let exact_work = context.allowance.binder_page_size - page_allowance.binder_page_size;
        let prepared = &mut search.prepared;
        let _phase_guard = context.profiling.as_ref().map(|p| {
            crate::profiling::QuantifierPhaseGuard::new(p.clone(), "input_binder_dependencies")
        });
        let scope = crate::rule_matching::scope::CandidateScope::AllCandidates;
        let mut batch = {
            let mut batch = prepared.candidates(
                context.graph,
                |term| context.smt.eval_to_string(term),
                crate::theories::quantifiers::BinderSearch::RequestPage(request, page_allowance),
                |cost_context| context.term_cost(cost_context, context.depth as u32),
                InstantiationOptions {
                    search_allowance: context.allowance,
                    additional_terms: vec![],
                    candidate_catalog: prepared.catalog.clone(),
                    candidate_scope: scope,
                    refinement_step: context.refinement_step,
                    selection_counts: context.selection_counts.clone(),
                    depth: context.depth,
                    instrumentation: InstantiationInstrumentation {
                        artifact_capture: context.artifact_capture,
                        profiling: context.profiling.clone(),
                    },
                },
            )?;
            batch.search.examined_substitutions += exact_work;
            batch
        };
        let mut known: std::collections::HashSet<_> = context
            .smt
            .get_instantiations()
            .iter()
            .map(canonical_instantiation_key)
            .collect();
        known.extend(context.pending_instances.iter().cloned());
        let summary = self.select_scheduled(&mut batch, exact, &known, context)?;
        for candidate in &mut batch.candidates {
            candidate.provenance = candidate
                .provenance
                .clone()
                .with_countermodel_origin(origin.clone());
        }
        if let Some(profiling) = &context.profiling {
            let mut p = profiling.borrow_mut();
            p.add_counter("input_binder_dependency_requests", 1);
            p.add_counter(
                "input_binder_dependency_instances_selected",
                summary.selected_binders as u64,
            );
            for (rule, counts) in summary.by_rule {
                p.record_rule_candidates(&rule, counts.generated, counts.selected);
                p.record_quantifier_counter(
                    &rule,
                    "dependency_instances_selected",
                    counts.selected as u64,
                );
            }
        }
        Ok(batch)
    }

    pub(crate) fn candidates<F: TermCostFactory + 'static>(
        &self,
        state: &mut Option<BinderSearchState>,
        phase: crate::theories::quantifiers::SearchPhase,
        context: &SearchContext<'_, F>,
        effort: &mut dyn crate::policy::ProofEffort,
    ) -> anyhow::Result<InstantiationBatch> {
        let smt = context.smt;
        let refinement_step = context.refinement_step;
        let profiling = &context.profiling;
        if self.plan.rules.is_empty() {
            return Ok(InstantiationBatch::default());
        }
        let _phase_guard = profiling
            .as_ref()
            .map(|p| crate::profiling::QuantifierPhaseGuard::new(p.clone(), phase.timing_key()));
        let phase_start = Instant::now();
        let search = state.as_mut().unwrap();
        // Graph growth resets match offsets and empty-pass conclusions. Exact
        // formula evaluations remain valid while this solver model is unchanged.
        if search.empty_passes.get(&phase).is_some_and(|cached| {
            cached.graph_version == context.graph_version
                && cached.refinement_step == refinement_step
                && cached.selection_counts == *context.selection_counts
                && cached.allowance == context.allowance
                && cached.pending_instances == *context.pending_instances
        }) {
            if let Some(profiling) = profiling {
                let mut profiling = profiling.borrow_mut();
                profiling.add_counter("input_binder_empty_passes_reused", 1);
                profiling.record_timing(phase.timing_key(), phase_start.elapsed());
            }
            let mut batch = InstantiationBatch::default();
            batch.search.cache_hit = true;
            batch.search.budget_exhausted_rules =
                search.empty_passes[&phase].budget_exhausted_rules.clone();
            return Ok(batch);
        }
        search.empty_passes.remove(&phase);
        let prepared = &mut search.prepared;
        prepared.start_phase(phase, 0);
        // Derived terms remain available for witnesses and nested binders.
        // Model-violation eligibility is independent of this vocabulary scope.
        let scope = crate::rule_matching::scope::CandidateScope::AllCandidates;
        let mut known: std::collections::HashSet<_> = context
            .smt
            .get_instantiations()
            .iter()
            .map(canonical_instantiation_key)
            .collect();
        known.extend(context.pending_instances.iter().cloned());
        let mut examined_total = 0;
        let mut returned_total = 0;
        loop {
            let pending = prepared.pending_rules(phase);
            if pending.is_empty() {
                search.empty_passes.insert(
                    phase,
                    BinderPassContext {
                        graph_version: context.graph_version,
                        refinement_step,
                        selection_counts: context.selection_counts.clone(),
                        allowance: context.allowance,
                        budget_exhausted_rules: Vec::new(),
                        pending_instances: context.pending_instances.clone(),
                    },
                );
                return Ok(InstantiationBatch::default());
            }
            let offered = profiling.as_ref().map(|_| {
                pending
                    .iter()
                    .map(|(index, _)| prepared.rule_description(phase, *index))
                    .chain(std::iter::once("ReturnToCoordinator".into()))
                    .collect::<Vec<_>>()
            });
            let choice_start = profiling.as_ref().map(|_| Instant::now());
            let choice = effort.choose_binder_rule(&crate::policy::effort::BinderEffortContext {
                phase,
                pending_rules: &pending,
                rule_count: prepared.rule_count(phase),
                background_rules: &self.plan.background_rules,
            });
            let choice_elapsed_secs = choice_start
                .map(|start| start.elapsed().as_secs_f64())
                .unwrap_or_default();
            let Some(rule) = choice else {
                if let Some(profiling) = &context.profiling {
                    profiling
                        .borrow_mut()
                        .record_effort(crate::policy::effort::EffortRecord {
                            model_version: context
                                .operation_id
                                .map(|id| id.model)
                                .unwrap_or_default(),
                            graph_version_before: context.graph_version,
                            graph_version: context.graph_version,
                            pending_instances: context.pending_instances.len(),
                            kind: crate::policy::effort::EffortRecordKind::BinderPage,
                            operation_id: context.operation_id,
                            operation: format!("{phase:?}:pause"),
                            chosen: "ReturnToCoordinator".into(),
                            offered: offered.clone().unwrap_or_default(),
                            allowance: None,
                            report: crate::policy::effort::WorkReport {
                                continuable: true,
                                ..Default::default()
                            },
                            candidates: Vec::new(),
                            choice_elapsed_secs,
                            elapsed_secs: 0.0,
                        });
                }
                // A policy pause is not evidence of an empty/exhausted pass.
                let mut batch = InstantiationBatch::default();
                batch.search.examined_substitutions = examined_total;
                batch.search.returned_substitutions = returned_total;
                batch.search.continuable_rules =
                    pending.into_iter().map(|(_, name)| name).collect();
                return Ok(batch);
            };
            anyhow::ensure!(
                pending.iter().any(|(i, _)| *i == rule),
                "effort chose an unavailable binder rule"
            );
            let page_start = Instant::now();
            let (exact, page_allowance) = if matches!(
                phase,
                super::SearchPhase::Witnesses | super::SearchPhase::TriggeredConflicts
            ) {
                self.scheduled_exact(
                    &mut search.exact_work,
                    &mut search.ground_terms,
                    &super::BinderSearchRequest {
                        helper: prepared.rule_helper(phase, rule).to_owned(),
                        phase,
                        bindings: Vec::new(),
                    },
                    context,
                )?
            } else {
                (None, context.allowance)
            };
            let exact_work = context.allowance.binder_page_size - page_allowance.binder_page_size;
            let helper = prepared.rule_helper(phase, rule).to_owned();
            let (directed, charged, directed_examined, directed_returned) = self
                .scheduled_indices(
                    prepared,
                    &mut search.demanded_indices,
                    &helper,
                    phase,
                    &context.with_allowance(page_allowance),
                    &known,
                )?;
            let mut page_allowance = page_allowance;
            page_allowance.binder_page_size -= charged;
            let mut batch = if let Some(batch) = directed {
                batch
            } else {
                prepared.candidates(
                    context.graph,
                    |term| smt.eval_to_string(term),
                    crate::theories::quantifiers::BinderSearch::Page {
                        phase,
                        rule,
                        allowance: page_allowance,
                    },
                    |cost_context| context.term_cost(cost_context, context.depth as u32),
                    InstantiationOptions {
                        search_allowance: context.allowance,
                        additional_terms: vec![],
                        candidate_catalog: prepared.catalog.clone(),
                        candidate_scope: scope,
                        refinement_step,
                        selection_counts: context.selection_counts.clone(),
                        depth: context.depth,
                        instrumentation: InstantiationInstrumentation {
                            artifact_capture: context.artifact_capture,
                            profiling: profiling.clone(),
                        },
                    },
                )?
            };
            batch.search.examined_substitutions += exact_work + directed_examined;
            batch.search.returned_substitutions += directed_returned;
            let selection_start = profiling.as_ref().map(|_| Instant::now());
            let summary = self.select_scheduled(&mut batch, exact, &known, context)?;
            if let Some(profiling) = profiling {
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
            let report = crate::policy::effort::WorkReport::from_batch(&batch);
            examined_total += report.examined_substitutions;
            returned_total += report.returned_substitutions;
            effort.observe(&crate::policy::effort::EffortEvent::BinderPage {
                phase,
                rule,
                rule_count: prepared.rule_count(phase),
                report: &report,
            });
            if let Some(profiling) = &context.profiling {
                profiling
                    .borrow_mut()
                    .record_effort(crate::policy::effort::EffortRecord {
                        model_version: context.operation_id.map(|id| id.model).unwrap_or_default(),
                        graph_version_before: context.graph_version,
                        graph_version: context.graph_version,
                        pending_instances: context.pending_instances.len(),
                        kind: crate::policy::effort::EffortRecordKind::BinderPage,
                        operation_id: context.operation_id,
                        chosen: prepared.rule_description(phase, rule),
                        candidates: crate::policy::effort::EffortCandidate::from_batch(&batch),
                        operation: format!(
                            "{phase:?}:{}",
                            pending.iter().find(|(i, _)| *i == rule).unwrap().1
                        ),
                        offered: offered.clone().unwrap_or_default(),
                        allowance: Some(context.allowance),
                        report: report.clone(),
                        choice_elapsed_secs,
                        elapsed_secs: page_start.elapsed().as_secs_f64(),
                    });
            }
            if batch.selected().next().is_some() || prepared.pending_rules(phase).is_empty() {
                if batch.selected().next().is_none() {
                    // Includes search-budget exhaustion: reuse the bounded
                    // result without claiming that no other matches exist.
                    search.empty_passes.insert(
                        phase,
                        BinderPassContext {
                            graph_version: context.graph_version,
                            refinement_step,
                            selection_counts: context.selection_counts.clone(),
                            allowance: context.allowance,
                            budget_exhausted_rules: batch.search.budget_exhausted_rules.clone(),
                            pending_instances: context.pending_instances.clone(),
                        },
                    );
                }
                if let Some(profiling) = profiling {
                    profiling
                        .borrow_mut()
                        .record_timing(phase.timing_key(), phase_start.elapsed());
                }
                batch.search.examined_substitutions = examined_total;
                batch.search.returned_substitutions = returned_total;
                return Ok(batch);
            }
            // Known/satisfied prefixes must not hide a later usable candidate.
            // Continuations share this model's graph and explicit work bound.
        }
    }
}

/// Keep ordinary winners and their cursor state; exact tuples only fill an
/// unproductive page after ordinary novelty and installation checks.
pub(super) fn select_ordinary_then_exact(
    batch: &mut InstantiationBatch,
    exact: Option<InstantiationBatch>,
    mut prepare: impl FnMut(
        &mut InstantiationBatch,
    ) -> anyhow::Result<crate::rule_matching::candidate::BatchSummary>,
) -> anyhow::Result<(crate::rule_matching::candidate::BatchSummary, bool)> {
    let summary = prepare(batch)?;
    let Some(exact) = exact else {
        return Ok((summary, false));
    };
    batch.search.returned_substitutions += exact.search.returned_substitutions;
    if batch.selected().next().is_some() {
        return Ok((summary, false));
    }
    batch.candidates.extend(exact.candidates);
    Ok((prepare(batch)?, true))
}
