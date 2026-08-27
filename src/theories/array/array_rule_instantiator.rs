use std::{cell::RefCell, collections::HashMap, rc::Rc, time::Instant};

use log::{debug, trace};

use crate::{
    auxiliary_synthesis::ArrayConflictRecord,
    cost_functions::YardbirdCostFunction,
    instantiation_provenance::InstantiationProvenance,
    profiling::ArrayProfilingCollector,
    theories::array::{
        array_axioms::{expr_to_term, ArrayLanguage, ArrayQuantifiedRule},
        array_grounding::{ground_pattern, instantiate_pattern, GroundContext, GroundSubstitution},
        array_term_extractor::ArrayTermExtractor,
        instantiation_candidate::{
            CandidateGroup, InstantiationCandidate, SelectionHistoryDecision,
        },
    },
    training::canonical_term_hash,
};

// Preserve the initial limit used by egg's `BackoffScheduler`, which this
// direct-search scheduler replaced. A smaller limit can truncate a conditional
// search before rejected substitutions are filtered out.
const INITIAL_RULE_MATCH_LIMIT: usize = 1_000;
const MAX_RULE_SEARCH_ROUNDS: usize = 15;

fn trace_conflicts_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

fn trace_conflicts(message: impl AsRef<str>) {
    trace!("[yardbird::conflict-trace] {}", message.as_ref());
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ArrayArtifactCapture {
    pub decisions: bool,
    pub instantiation_provenance: bool,
    pub conflicts: bool,
}

pub struct ArrayRuleInstantiatorOptions {
    pub refinement_step: u32,
    pub depth: u16,
    pub artifact_capture: ArrayArtifactCapture,
    pub profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

pub struct ArrayRuleInstantiator<CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    candidates: Vec<InstantiationCandidate>,
    selection_history: Vec<SelectionHistoryDecision>,
    artifact_capture: ArrayArtifactCapture,
    next_instantiation_ordinal: usize,
    pub cost_fn: CF,
    extractor: ArrayTermExtractor<CF>,
    refinement_step: u32,
    depth: u16,
    profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

impl<CF> ArrayRuleInstantiator<CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    pub fn new(
        cost_fn: CF,
        extractor: ArrayTermExtractor<CF>,
        options: ArrayRuleInstantiatorOptions,
    ) -> Self {
        let ArrayRuleInstantiatorOptions {
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
            extractor,
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

impl<CF> ArrayRuleInstantiator<CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    pub(crate) fn search_rules<N>(
        &mut self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        rules: &[ArrayQuantifiedRule<N>],
    ) -> usize
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        // A broad quantified rule should not monopolize one search pass. Start
        // with a bounded search and double only the limits of rules that exceed
        // it. This retains egg's former BackoffScheduler behavior without
        // modeling quantified rules as rewrites.
        let mut times_over_limit = vec![0u32; rules.len()];
        for round in 0..MAX_RULE_SEARCH_ROUNDS {
            let mut any_rule_over_limit = false;
            let mut matches_by_rule = Vec::with_capacity(rules.len());

            for (rule_index, rule) in rules.iter().enumerate() {
                let threshold = INITIAL_RULE_MATCH_LIMIT
                    .checked_shl(times_over_limit[rule_index])
                    .unwrap_or(usize::MAX);
                let search_start = Instant::now();
                let mut matches = rule.search_with_limit(egraph, threshold.saturating_add(1));
                let substitutions = matches
                    .iter()
                    .map(|search_match| search_match.substs.len())
                    .sum::<usize>();
                let over_limit = substitutions > threshold;
                if over_limit {
                    times_over_limit[rule_index] += 1;
                    any_rule_over_limit = true;
                    matches.clear();
                }
                if let Some(profiling) = &self.profiling {
                    profiling.borrow_mut().record_rule_search(
                        rule.metadata().name(),
                        matches.len(),
                        if over_limit { 0 } else { substitutions },
                        search_start.elapsed(),
                    );
                }
                if trace_conflicts_enabled() {
                    trace_conflicts(format!(
                        "search round={round} rule={} eclasses={} matches={} substitutions={} threshold={} backed_off={} existing_insts={}",
                        rule.metadata().name(),
                        egraph.number_of_classes(),
                        matches.len(),
                        substitutions,
                        threshold,
                        over_limit,
                        self.candidates.len()
                    ));
                    for (match_ix, search_match) in matches.iter().enumerate() {
                        trace_conflicts(format!(
                            "  match[{match_ix}] eclass={} subst_count={}",
                            search_match.eclass,
                            search_match.substs.len(),
                        ));
                    }
                }
                matches_by_rule.push(matches);
            }

            for (rule, matches) in rules.iter().zip(matches_by_rule) {
                self.instantiate_rule(egraph, rule, matches);
            }

            if !any_rule_over_limit {
                return round + 1;
            }
        }

        MAX_RULE_SEARCH_ROUNDS
    }

    fn instantiate_rule<'a, N>(
        &mut self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        executable_rule: &'a ArrayQuantifiedRule<N>,
        matches: Vec<egg::SearchMatches<'a, ArrayLanguage>>,
    ) where
        N: egg::Analysis<ArrayLanguage>,
    {
        let rule = executable_rule.metadata();
        let apply_start = Instant::now();
        let mut substitutions_explored = 0usize;
        let tracing = trace_conflicts_enabled();
        debug!("======>");
        debug!(
            "instantiate_rule: {} with {} matches, inst_count={}",
            rule.name(),
            matches.len(),
            self.candidates.len()
        );
        if tracing {
            trace_conflicts(format!(
                "instantiate rule={} matches={} existing_insts={}",
                rule.name(),
                matches.len(),
                self.candidates.len()
            ));
        }
        let rank_complete_instantiations = self.extractor.explores_all_matches();
        let searcher_ast = executable_rule.trigger();
        let consequence_ast = executable_rule.consequence();

        for (match_ix, m) in matches.iter().enumerate() {
            debug!("Number of subs: {}", m.substs.len());
            if tracing {
                trace_conflicts(format!(
                    "  exploring match[{match_ix}] eclass={} subst_count={}",
                    m.eclass,
                    m.substs.len()
                ));
            }
            for (subst_ix, subst) in m.substs.iter().enumerate() {
                substitutions_explored += 1;
                debug!("Current Sub: {:?}", subst);
                if tracing {
                    trace_conflicts(format!("    subst[{subst_ix}] raw={subst:?}"));
                }

                let context = GroundContext::new(
                    self.artifact_capture.decisions,
                    rule.name(),
                    rule.category(),
                );

                let mut grounding = GroundSubstitution::default();

                ground_pattern(
                    searcher_ast,
                    Some(m.eclass),
                    subst,
                    &mut grounding,
                    egraph,
                    &self.extractor,
                    context,
                )
                .expect("egg search must bind every trigger variable.");

                let new_lhs = instantiate_pattern(searcher_ast, &grounding)
                    .expect("Fully grounded trigger must be instantiable.");
                let new_rhs = instantiate_pattern(consequence_ast, &grounding)
                    .expect("Fully grounded consequence must be instantiable.");

                let mut decisions = grounding.decisions().to_vec();
                let mut selection_history = grounding.selection_history().to_vec();
                let used_derived_candidate = grounding.used_derived_candidate();

                if self.extractor.requires_source_grounded_candidates() && used_derived_candidate {
                    if tracing {
                        trace_conflicts(format!(
                                    "    subst[{subst_ix}] skipped because cone selection required a derived candidate"
                                ));
                    }
                    continue;
                }

                let rhs_eclass = egraph.lookup_expr(&new_rhs);
                if tracing {
                    trace_conflicts(format!(
                                "    subst[{subst_ix}] lhs={} rhs={} lhs_eclass={} rhs_eclass={rhs_eclass:?}",
                                new_lhs,
                                new_rhs,
                                m.eclass
                            ));
                }
                // the eclass that we would have inserted from this pattern
                // would cause a union from `rhs_eclass` to `eclass`. This means it
                // is creating an equality that wouldn't otherwise be in the
                // e-graph. This is a conflict, so we record the rule instantiation
                // here.
                if Some(m.eclass) != rhs_eclass {
                    let instantiation = instantiate_pattern(executable_rule.formula(), &grounding)
                        .expect("Fully grounded rule formula must be instantiable.");

                    let ordinal = self.next_instantiation_ordinal;
                    self.next_instantiation_ordinal += 1;
                    let instantiation_hash = canonical_term_hash(&instantiation);
                    if rank_complete_instantiations && self.artifact_capture.decisions {
                        for decision in &mut decisions {
                            decision.decision_key =
                                format!("{}:candidate:{instantiation_hash}", decision.decision_key);
                        }
                        for decision in &mut selection_history {
                            decision.decision_key =
                                format!("{}:candidate:{instantiation_hash}", decision.decision_key);
                        }
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
                    let cost_expression = if rank_complete_instantiations {
                        &instantiation
                    } else {
                        &new_rhs
                    };
                    let cost_site = if rank_complete_instantiations {
                        "complete_instantiation_ranking"
                    } else {
                        "consequence_ranking"
                    };
                    let cost = if let Some(profiling) = &self.profiling {
                        let mut cost_fn = self.cost_fn.clone();
                        profiling.borrow_mut().record_cost(
                            cost_site,
                            cost_expression.as_ref().len(),
                            || cost_fn.cost_rec(cost_expression),
                        )
                    } else {
                        self.cost_fn.cost_rec(cost_expression)
                    };

                    let conflict = self.artifact_capture.conflicts.then(|| {
                        ArrayConflictRecord::new(
                            ordinal,
                            abstract_instantiation_id.clone(),
                            rule.name(),
                            instantiation.clone(),
                            expr_to_term(instantiation.clone()),
                            self.depth,
                            self.refinement_step,
                            cost,
                            decision_keys,
                        )
                    });
                    let abstract_instantiation = self
                        .artifact_capture
                        .instantiation_provenance
                        .then_some(abstract_instantiation);
                    let candidate = InstantiationCandidate {
                        rule: rule.clone(),
                        expression: instantiation.clone(),
                        cost,
                        provenance: InstantiationProvenance::new(
                            abstract_instantiation_id,
                            substitution,
                        ),
                        selected: false,
                        decisions,
                        selection_history,
                        abstract_instantiation,
                        conflict,
                        group: CandidateGroup::MatchRoot(egraph.find(m.eclass)),
                    };
                    if tracing {
                        trace_conflicts(format!(
                            "    subst[{subst_ix}] conflict cost={} instantiation={}",
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
                    self.candidates.push(candidate);
                } else {
                    self.record_selection_history(&selection_history);
                    if tracing {
                        trace_conflicts(format!(
                            "    subst[{subst_ix}] no conflict because rhs already maps to eclass {}",
                            m.eclass
                        ));
                    }
                }
            }
        }
        debug!("<======");
        if let Some(profiling) = &self.profiling {
            profiling.borrow_mut().record_rule_instantiation(
                rule.name(),
                substitutions_explored,
                false,
                apply_start.elapsed(),
            );
        }
    }
}
