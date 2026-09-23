//! Shared matching and complete-instance construction.
use crate::policy::term_selection::YardbirdCostFunction;
use crate::problem_context::ArrayCandidateCatalog;
use crate::profiling::RefinementProfilingCollector;
use crate::rule_matching::candidate::InstantiationBatch;
use crate::rule_matching::candidate::{
    InstantiationCandidate, InstantiationGrounding, SelectionHistoryDecision,
};
use crate::rule_matching::compiled_rule::CompiledQuantifiedRule;
use crate::rule_matching::extractor::{TermExtractor, TermExtractorOptions};
use crate::rule_matching::grounding::{
    groundings, instantiate_pattern, GroundContext, GroundSubstitution,
};
use crate::rule_matching::provenance::InstantiationProvenance;
use crate::rule_matching::scope::CandidateScope;
use crate::terms::language::expr_to_term;
use crate::terms::language::{TermExpr, TermLanguage};
use crate::training::canonical_term_hash;
use egg::*;
use log::{debug, trace};
use rustc_hash::FxHashMap;
use std::collections::HashMap;
use std::{cell::RefCell, rc::Rc, time::Instant};

pub struct InstantiationInstrumentation {
    pub artifact_capture: ArtifactCapture,
    pub profiling: Option<Rc<RefCell<RefinementProfilingCollector>>>,
}

pub struct InstantiationOptions {
    pub search_allowance: crate::policy::effort::WorkAllowance,
    pub candidate_catalog: ArrayCandidateCatalog,
    pub additional_terms: Vec<TermExpr>,
    pub candidate_scope: CandidateScope,
    pub refinement_step: u32,
    pub selection_counts: FxHashMap<String, u32>,
    pub depth: u16,
    pub instrumentation: InstantiationInstrumentation,
}

fn egraph_node_count<N>(egraph: &EGraph<TermLanguage, N>) -> usize
where
    N: Analysis<TermLanguage>,
{
    egraph.classes().map(|class| class.nodes.len()).sum()
}

/// Ground only matches that passed the caller's semantic eligibility check.
pub(crate) fn instantiate_quantified_matches<CF, N, M>(
    egraph: &EGraph<TermLanguage, N>,
    make_cost: impl FnOnce() -> CF,
    rules: &[CompiledQuantifiedRule<N, M>],
    options: InstantiationOptions,
    matched: crate::rule_matching::search::MatchedRules,
    demand: Option<CandidateDemand<'_>>,
    needed_classes: Option<&std::collections::HashSet<Id>>,
) -> anyhow::Result<InstantiationBatch>
where
    N: Analysis<TermLanguage> + 'static,
    CF: YardbirdCostFunction<TermLanguage> + 'static,
{
    let InstantiationOptions {
        search_allowance: _,
        candidate_catalog,
        additional_terms,
        candidate_scope,
        refinement_step,
        selection_counts,
        depth,
        instrumentation,
    } = options;
    let InstantiationInstrumentation {
        artifact_capture,
        profiling,
    } = instrumentation;
    if let Some(profiling) = &profiling {
        profiling
            .borrow_mut()
            .set_egraph_before_rule_search(egraph.number_of_classes(), egraph_node_count(egraph));
    }
    if let Some(profiling) = &profiling {
        let mut profiling = profiling.borrow_mut();
        profiling.add_counter(
            "rule_search_substitutions_examined",
            matched.report.examined_substitutions as u64,
        );
        profiling.add_counter(
            "rule_search_continuations_available",
            matched.report.continuable_rules.len() as u64,
        );
        profiling.add_counter(
            "rule_search_budget_exhausted",
            matched.report.budget_exhausted_rules.len() as u64,
        );
    }
    if matched.matches.is_empty() {
        return Ok(InstantiationBatch {
            candidates: vec![],
            search: matched.report,
        });
    }
    let cost_fn = make_cost();
    let instantiation_cost_fn = cost_fn.clone();
    let extractor_start = Instant::now();
    let mut extractor = TermExtractor::for_eclasses(
        egraph,
        cost_fn,
        TermExtractorOptions {
            candidate_catalog,
            candidate_scope,
            refinement_step,
            selection_counts,
            depth,
            profiling: profiling.clone(),
        },
        needed_classes,
    );
    extractor.admit_terms_for_eclasses(egraph, &additional_terms, needed_classes);
    if let Some(profiling) = &profiling {
        profiling
            .borrow_mut()
            .record_timing("extractor_init", extractor_start.elapsed());
    }
    let mut instantiator = CandidateBuilder::new(
        instantiation_cost_fn,
        extractor,
        CandidateBuilderOptions {
            refinement_step,
            depth,
            artifact_capture,
            profiling: profiling.clone(),
        },
    );
    let grounding_start = Instant::now();
    let search_rounds = matched.report.rounds;
    instantiator.instantiate_matches(egraph, rules, matched.matches, demand)?;
    if let Some(profiling) = &profiling {
        profiling
            .borrow_mut()
            .record_timing("rule_grounding_total", grounding_start.elapsed());
        profiling.borrow_mut().set_egraph_after_rule_search(
            egraph.number_of_classes(),
            egraph_node_count(egraph),
            search_rounds,
        );
    }

    let candidates = instantiator.into_candidates();

    #[cfg(debug_assertions)]
    {
        log::debug!("=== FINAL INSTANTIATIONS ===");
        for (index, candidate) in candidates.iter().enumerate() {
            log::debug!("  [{}] {}", index, candidate.expression);
        }
        log::debug!("============================\n");
    }

    Ok(InstantiationBatch {
        candidates,
        search: matched.report,
    })
}

fn trace_conflicts_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

fn trace_conflicts(message: impl AsRef<str>) {
    trace!("[yardbird::conflict-trace] {}", message.as_ref());
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ArtifactCapture {
    pub decisions: bool,
    pub instantiation_provenance: bool,
    pub conflicts: bool,
}

/// Demand for usable candidates; rejected proposals do not consume the budget.
pub(crate) struct CandidateDemand<'a> {
    pub budget: usize,
    pub accept: &'a mut dyn FnMut(&mut InstantiationCandidate) -> anyhow::Result<bool>,
}

fn round_robin<I: Iterator>(streams: impl IntoIterator<Item = I>) -> impl Iterator<Item = I::Item> {
    let mut queue = streams
        .into_iter()
        .collect::<std::collections::VecDeque<_>>();
    std::iter::from_fn(move || loop {
        let mut stream = queue.pop_front()?;
        if let Some(item) = stream.next() {
            queue.push_back(stream);
            return Some(item);
        }
    })
}

struct CandidateBuilderOptions {
    pub refinement_step: u32,
    pub depth: u16,
    pub artifact_capture: ArtifactCapture,
    pub profiling: Option<Rc<RefCell<RefinementProfilingCollector>>>,
}

struct CandidateBuilder<CF>
where
    CF: YardbirdCostFunction<TermLanguage>,
{
    candidates: Vec<InstantiationCandidate>,
    selection_history: Vec<SelectionHistoryDecision>,
    artifact_capture: ArtifactCapture,
    next_instantiation_ordinal: usize,
    cost_fn: CF,
    extractor: Rc<TermExtractor<CF>>,
    refinement_step: u32,
    depth: u16,
    profiling: Option<Rc<RefCell<RefinementProfilingCollector>>>,
}

impl<CF> CandidateBuilder<CF>
where
    CF: YardbirdCostFunction<TermLanguage>,
{
    pub fn new(
        cost_fn: CF,
        extractor: TermExtractor<CF>,
        options: CandidateBuilderOptions,
    ) -> Self {
        let CandidateBuilderOptions {
            refinement_step,
            depth,
            artifact_capture,
            profiling,
        } = options;
        Self {
            candidates: vec![],
            selection_history: vec![],
            artifact_capture,
            next_instantiation_ordinal: 0,
            cost_fn,
            extractor: Rc::new(extractor),
            refinement_step,
            depth,
            profiling,
        }
    }

    pub(crate) fn into_candidates(mut self) -> Vec<InstantiationCandidate> {
        let latest_selection = self
            .selection_history
            .into_iter()
            .map(|decision| (decision.decision_key, decision.chosen_term_hash))
            .collect::<HashMap<_, _>>();
        for candidate in &mut self.candidates {
            for decision in &mut candidate.selection_history {
                if let Some(chosen_term_hash) = latest_selection.get(&decision.decision_key) {
                    decision.chosen_term_hash = chosen_term_hash.clone();
                }
            }
        }
        self.candidates
    }

    fn record_selection_history(&mut self, decisions: &[SelectionHistoryDecision]) {
        self.selection_history.extend_from_slice(decisions);
    }
}

impl<CF> CandidateBuilder<CF>
where
    CF: YardbirdCostFunction<TermLanguage>,
{
    pub(crate) fn instantiate_matches<N, M>(
        &mut self,
        egraph: &egg::EGraph<TermLanguage, N>,
        rules: &[CompiledQuantifiedRule<N, M>],
        pending: Vec<crate::rule_matching::search::RuleMatch>,
        mut demand: Option<CandidateDemand<'_>>,
    ) -> anyhow::Result<()>
    where
        N: egg::Analysis<TermLanguage>,
    {
        let first_round = pending.len();
        let streams = pending
            .into_iter()
            .map(|matched| {
                let crate::rule_matching::search::RuleMatch {
                    rule_index,
                    root,
                    substitution: subst,
                    model_violation_verified,
                } = matched;
                let rule = &rules[rule_index];
                let profiling = self.profiling.is_some();
                let mut choices = groundings(
                    rule.trigger(),
                    root,
                    subst,
                    egraph,
                    self.extractor.clone(),
                    GroundContext::new(
                        self.artifact_capture.decisions,
                        rule.metadata().name(),
                        rule.metadata().category(),
                    ),
                );
                std::iter::from_fn(move || {
                    let start = profiling.then(Instant::now);
                    let grounding = choices.next()?;
                    Some((
                        rule_index,
                        root,
                        grounding,
                        model_violation_verified,
                        start.map(|start| start.elapsed()).unwrap_or_default(),
                    ))
                })
            })
            .collect::<Vec<_>>();
        let mut work = round_robin(streams);
        let budget = demand.as_ref().map(|demand| demand.budget);
        let mut visit =
            |(rule_index, root, grounding, verified, grounding_time)| -> anyhow::Result<usize> {
                let Some(mut candidate) = self.instantiate_grounding(
                    egraph,
                    &rules[rule_index],
                    root,
                    grounding,
                    grounding_time,
                ) else {
                    return Ok(0);
                };
                candidate.model_violation_verified = verified;
                let accepted = if let Some(demand) = demand.as_mut() {
                    (demand.accept)(&mut candidate)?
                } else {
                    true
                };
                self.candidates.push(candidate);
                Ok(usize::from(accepted))
            };
        let mut accepted = 0;
        // Preserve the existing first pass and let the whole-candidate ranker
        // compare its proposals. Only underfilled source batches explore more.
        for item in work.by_ref().take(first_round) {
            accepted += visit(item)?;
        }
        if let Some(budget) = budget {
            while accepted < budget {
                let Some(item) = work.next() else {
                    break;
                };
                accepted += visit(item)?;
            }
        }
        Ok(())
    }

    fn instantiate_grounding<N, M>(
        &mut self,
        egraph: &egg::EGraph<TermLanguage, N>,
        executable_rule: &CompiledQuantifiedRule<N, M>,
        root: egg::Id,
        grounding: GroundSubstitution,
        grounding_time: std::time::Duration,
    ) -> Option<InstantiationCandidate>
    where
        N: egg::Analysis<TermLanguage>,
    {
        let rule = executable_rule.metadata();
        let tracing = trace_conflicts_enabled();
        let searcher_ast = executable_rule.trigger();
        let apply_start = Instant::now();
        let candidate = {
            let mut decisions = grounding.decisions().to_vec();
            let mut selection_history = grounding.selection_history().to_vec();
            let used_derived_candidate = grounding.used_derived_candidate()
                || executable_rule
                    .fixed_bindings()
                    .iter()
                    .any(|(_, expression)| {
                        egraph.lookup_expr(expression).is_none_or(|id| {
                            self.extractor.candidate_origin(egraph, id, expression)
                                == crate::rule_matching::extractor::CandidateOrigin::Derived
                        })
                    });
            let is_conflict = if let Some(consequence_ast) = executable_rule.consequence() {
                let new_rhs = instantiate_pattern(consequence_ast, &grounding)
                    .expect("Fully grounded consequence must be instantiable.");
                let rhs_eclass = egraph.lookup_expr(&new_rhs);
                if tracing {
                    let new_lhs = instantiate_pattern(searcher_ast, &grounding)
                        .expect("Fully grounded trigger must be instantiable.");
                    trace_conflicts(format!(
                        "    grounding lhs={} rhs={} lhs_eclass={} rhs_eclass={rhs_eclass:?}",
                        new_lhs, new_rhs, root
                    ));
                }
                Some(root) != rhs_eclass
            } else {
                // An arbitrary Boolean rule has no equality-union shortcut.
                // Build its formula once; batch preparation checks the model.
                true
            };
            if is_conflict {
                let instantiation = instantiate_pattern(executable_rule.formula(), &grounding)
                    .expect("Fully grounded rule formula must be instantiable.");

                let ordinal = self.next_instantiation_ordinal;
                self.next_instantiation_ordinal += 1;
                let instantiation_hash = canonical_term_hash(&instantiation);
                for decision in &mut decisions {
                    decision.decision_key =
                        format!("{}:candidate:{instantiation_hash}", decision.decision_key);
                }
                for decision in &mut selection_history {
                    decision.decision_key =
                        format!("{}:candidate:{instantiation_hash}", decision.decision_key);
                }
                self.record_selection_history(&selection_history);
                let selection_decision_keys = selection_history
                    .iter()
                    .map(|decision| decision.decision_key.clone())
                    .collect::<Vec<_>>();
                let decision_keys = if self.artifact_capture.decisions {
                    selection_decision_keys.clone()
                } else {
                    vec![]
                };
                let mut substitution = grounding
                    .variable_expressions()
                    .chain(
                        executable_rule
                            .fixed_bindings()
                            .iter()
                            .map(|(var, expr)| (*var, expr)),
                    )
                    .map(|(variable, expression)| {
                        (variable.to_string(), expr_to_term(expression.clone()))
                    })
                    .collect::<Vec<_>>();
                substitution.sort_by(|left, right| left.0.cmp(&right.0));

                let (_, substitution) = smt2parser::vmt::UnquantifiedInstantiator::rewrite_unquantified_with_substitution(
                    expr_to_term(instantiation.clone()),
                    vec![],
                    substitution,
                )
                .expect("array candidates should have a relative-frame substitution");
                let abstract_instantiation = self.extractor.abstract_instantiation_record(
                    rule.name(),
                    &instantiation,
                    decision_keys.clone(),
                    &substitution,
                );
                let abstract_instantiation_id =
                    abstract_instantiation.abstract_instantiation_id.clone();
                let cost_expression = &instantiation;
                let cost_site = "complete_instantiation_ranking";
                let cost = if let Some(profiling) = self.profiling.clone() {
                    profiling.borrow_mut().record_cost(
                        cost_site,
                        cost_expression.as_ref().len(),
                        || self.cost_fn.cost_rec(cost_expression),
                    )
                } else {
                    self.cost_fn.cost_rec(cost_expression)
                };

                let abstract_instantiation = self
                    .artifact_capture
                    .instantiation_provenance
                    .then_some(abstract_instantiation);
                let mut candidate = InstantiationCandidate {
                    rule: rule.clone(),
                    expression: instantiation.clone(),
                    cost,
                    grounding: if used_derived_candidate {
                        InstantiationGrounding::Derived
                    } else {
                        InstantiationGrounding::SourceGrounded
                    },
                    provenance: InstantiationProvenance::new(
                        abstract_instantiation_id,
                        substitution,
                    ),
                    selected: false,
                    decisions,
                    selection_history,
                    abstract_instantiation,
                    conflict: None,
                    group: executable_rule.group(egraph.find(root)),
                    model_violation_verified: false,
                };
                if self.artifact_capture.conflicts {
                    crate::theories::array::candidate::capture_conflict(
                        &mut candidate,
                        ordinal,
                        self.depth,
                        self.refinement_step,
                        decision_keys,
                    );
                }
                if tracing {
                    trace_conflicts(format!(
                        "    grounding conflict cost={} instantiation={}",
                        cost, instantiation
                    ));
                }
                debug!(
                    "FOUND VIOLATION (cost {}): \n{}",
                    cost,
                    instantiation.pretty(80)
                );

                if tracing {
                    trace_conflicts("    accepted instantiation candidate");
                }
                Some(candidate)
            } else {
                self.record_selection_history(&selection_history);
                if tracing {
                    trace_conflicts(format!(
                        "    grounding no conflict because rhs already maps to eclass {}",
                        root
                    ));
                }
                None
            }
        };
        if let Some(profiling) = &self.profiling {
            profiling.borrow_mut().record_rule_instantiation(
                rule.name(),
                1,
                false,
                grounding_time + apply_start.elapsed(),
            );
        }
        candidate
    }
}
