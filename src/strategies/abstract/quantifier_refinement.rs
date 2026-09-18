//! Input-binder compilation and search. Policy-owned rotation survives solver checks;
//! prepared matches and empty-pass caches belong to one model in coordinator state.
use super::search_context::SearchContext;
use crate::{
    cost_functions::array::ArrayCostFactory,
    instantiation_strategy::assertion_tracker::canonical_instantiation_key,
    profiling::ArrayProfilingCollector,
    theories::array::{
        array_axioms::{ArrayInstantiationInstrumentation, ArrayInstantiationOptions},
        instantiation_candidate::InstantiationBatch,
    },
};
use log::info;
use rustc_hash::FxHashMap;
use smt2parser::vmt::VMTModel;
use std::{cell::RefCell, collections::HashMap, rc::Rc, time::Instant};

#[derive(Default)]
pub(super) struct QuantifierRefinement {
    pub(super) plan: crate::quantifier_abstraction::QuantifierPlan,
    pub(super) provenance: crate::quantifier_provenance::QuantifierProvenance,
    pub(super) configuration_error: Option<String>,
    pub(super) owns_quantifiers: bool,
}

/// One solver model's fixed binder graph and unsuccessful selection passes.
pub(crate) struct BinderSearchState {
    prepared: crate::quantifier_abstraction::PreparedQuantifierSearch,
    empty_passes: HashMap<crate::quantifier_abstraction::SearchPhase, BinderPassContext>,
    pub(super) requests: Vec<DependencyWork>,
    pub(super) dependencies_searched: bool,
}

pub(super) struct DependencyWork {
    pub(super) request: crate::quantifier_abstraction::BinderSearchRequest,
    pub(super) description: String,
}

struct BinderPassContext {
    refinement_step: u32,
    selection_counts: FxHashMap<String, u32>,
    allowance: crate::policy::effort::WorkAllowance,
    budget_exhausted_rules: Vec<String>,
    pending_instances: std::collections::HashSet<smt2parser::concrete::Term>,
}

impl QuantifierRefinement {
    pub(super) fn configure_model(&mut self, model: VMTModel, profile: bool) -> VMTModel {
        self.configuration_error = None;
        self.owns_quantifiers = model.as_commands().iter().any(|command| match command {
            smt2parser::concrete::Command::DefineFun { term, .. }
            | smt2parser::concrete::Command::Assert { term } => {
                crate::quantifier_abstraction::contains_binders(term)
            }
            _ => false,
        });
        let model = match crate::quantifier_provenance::scope_model(model.clone(), profile) {
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
        self.provenance.record_property_witnesses(&bindings);
        let herbrand_witnesses = bindings.len();
        if herbrand_witnesses > 0 {
            info!("Herbrandized universal property with {herbrand_witnesses} witness constants");
        }
        let original = model.clone();
        match crate::quantifier_abstraction::lower_model_with_provenance(
            model,
            &mut self.provenance,
        ) {
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

    fn prepare_binder_search(
        &self,
        smt: &dyn crate::problem_context::ProblemContext,
        state: &mut Option<BinderSearchState>,
        profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
    ) -> anyhow::Result<()> {
        if state.is_none() {
            let start = Instant::now();
            *state = Some(BinderSearchState {
                prepared: self.plan.prepare(smt)?,
                empty_passes: HashMap::new(),
                dependencies_searched: false,
                requests: Vec::new(),
            });
            if let Some(profiling) = profiling {
                let mut profiling = profiling.borrow_mut();
                profiling.record_timing("input_binder_prepare", start.elapsed());
                profiling.add_counter("input_binder_model_preparations", 1);
            }
        }
        Ok(())
    }

    pub(super) fn discover<F: ArrayCostFactory + 'static>(
        &mut self,
        state: &mut Option<BinderSearchState>,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<crate::policy::effort::WorkReport> {
        self.prepare_binder_search(context.smt, state, &context.profiling)?;
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
        let mut seen = std::collections::HashSet::new();
        search.requests.clear();
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

    pub(super) fn dependency_request<F: ArrayCostFactory + 'static>(
        &mut self,
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
        let request = &request.request;
        let prepared = &mut search.prepared;
        let _phase_guard = context.profiling.as_ref().map(|p| {
            crate::profiling::QuantifierPhaseGuard::new(p.clone(), "input_binder_dependencies")
        });
        let scope = crate::theories::array::candidate_scope::CandidateScope::AllCandidates;
        let mut batch = prepared.candidates(
            |term| context.smt.eval_to_string(term),
            crate::quantifier_abstraction::BinderSearch::RequestPage(request, context.allowance),
            |cost_context| context.term_cost(cost_context, context.depth as u32),
            ArrayInstantiationOptions {
                search_allowance: context.allowance,
                additional_terms: vec![],
                candidate_catalog: prepared.catalog.clone(),
                candidate_scope: scope,
                refinement_step: context.refinement_step,
                selection_counts: context.selection_counts.clone(),
                depth: context.depth,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture: context.artifact_capture,
                    profiling: context.profiling.clone(),
                },
            },
        )?;
        let mut known: std::collections::HashSet<_> = context
            .smt
            .get_instantiations()
            .iter()
            .map(canonical_instantiation_key)
            .collect();
        known.extend(context.pending_instances.iter().cloned());
        let summary = batch.prepare_with_ranker(
            scope,
            &known,
            context.allowance.winners,
            context.ranker,
            |term| context.smt.eval_to_string(term),
            |c| context.installable_expression(&c.expression),
        )?;
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

    pub(super) fn candidates<F: ArrayCostFactory + 'static>(
        &mut self,
        state: &mut Option<BinderSearchState>,
        phase: crate::quantifier_abstraction::SearchPhase,
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
        self.prepare_binder_search(smt, state, profiling)?;
        let search = state.as_mut().unwrap();
        // Widening the array graph leaves the prepared binder graph, model,
        // known instances, cost configuration and ranker unchanged. Only
        // representative-use history may change between these attempts.
        if search.empty_passes.get(&phase).is_some_and(|cached| {
            cached.refinement_step == refinement_step
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
            batch.search.budget_exhausted_rules =
                search.empty_passes[&phase].budget_exhausted_rules.clone();
            return Ok(batch);
        }
        search.empty_passes.remove(&phase);
        let prepared = &mut search.prepared;
        prepared.start_phase(phase, 0);
        // Derived terms remain available for witnesses and nested binders.
        // Model-violation eligibility is independent of this vocabulary scope.
        let scope = crate::theories::array::candidate_scope::CandidateScope::AllCandidates;
        let mut known: std::collections::HashSet<_> = smt
            .get_instantiations()
            .iter()
            .map(canonical_instantiation_key)
            .collect();
        known.extend(context.pending_instances.iter().cloned());
        let mut examined_total = 0;
        loop {
            let pending = prepared.pending_rules(phase);
            if pending.is_empty() {
                search.empty_passes.insert(
                    phase,
                    BinderPassContext {
                        refinement_step,
                        selection_counts: context.selection_counts.clone(),
                        allowance: context.allowance,
                        budget_exhausted_rules: Vec::new(),
                        pending_instances: context.pending_instances.clone(),
                    },
                );
                return Ok(InstantiationBatch::default());
            }
            let Some(rule) =
                effort.choose_binder_rule(&crate::policy::effort::BinderEffortContext {
                    phase,
                    pending_rules: &pending,
                    rule_count: prepared.rule_count(phase),
                })
            else {
                // A policy pause is not evidence of an empty/exhausted pass.
                let mut batch = InstantiationBatch::default();
                batch.search.examined_substitutions = examined_total;
                batch.search.continuable_rules =
                    pending.into_iter().map(|(_, name)| name).collect();
                return Ok(batch);
            };
            anyhow::ensure!(
                pending.iter().any(|(i, _)| *i == rule),
                "effort chose an unavailable binder rule"
            );
            let page_start = Instant::now();
            let mut batch = prepared.candidates(
                |term| smt.eval_to_string(term),
                crate::quantifier_abstraction::BinderSearch::Page {
                    phase,
                    rule,
                    allowance: context.allowance,
                },
                |cost_context| context.term_cost(cost_context, context.depth as u32),
                ArrayInstantiationOptions {
                    search_allowance: context.allowance,
                    additional_terms: vec![],
                    candidate_catalog: prepared.catalog.clone(),
                    candidate_scope: scope,
                    refinement_step,
                    selection_counts: context.selection_counts.clone(),
                    depth: context.depth,
                    instrumentation: ArrayInstantiationInstrumentation {
                        artifact_capture: context.artifact_capture,
                        profiling: profiling.clone(),
                    },
                },
            )?;
            let selection_start = profiling.as_ref().map(|_| Instant::now());
            let summary = batch.prepare_with_ranker(
                scope,
                &known,
                context.allowance.winners,
                context.ranker,
                |term| smt.eval_to_string(term),
                |candidate| context.installable_expression(&candidate.expression),
            )?;
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
                        operation_id: context.operation_id,
                        operation: format!(
                            "{phase:?}:{}",
                            pending.iter().find(|(i, _)| *i == rule).unwrap().1
                        ),
                        offered: pending.iter().map(|(_, name)| name.clone()).collect(),
                        allowance: context.allowance,
                        report: report.clone(),
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
                return Ok(batch);
            }
            // Known/satisfied prefixes must not hide a later usable candidate.
            // Continuations share this model's graph and explicit work bound.
        }
    }
}
