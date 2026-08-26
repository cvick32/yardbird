use std::{cell::RefCell, collections::HashMap, rc::Rc, time::Instant};

use egg::{Analysis, Language};
use log::{debug, trace};

use crate::{
    auxiliary_synthesis::ArrayConflictRecord,
    cost_functions::YardbirdCostFunction,
    egg_utils::RecExprRoot,
    instantiation_provenance::InstantiationProvenance,
    profiling::ArrayProfilingCollector,
    theories::array::{
        array_axioms::{expr_to_term, ArrayExpr, ArrayLanguage, ArrayQuantifiedRule},
        array_term_extractor::{ArrayTermExtractor, CandidateOrigin},
        instantiation_candidate::{
            CandidateGroup, InstantiationCandidate, SelectionHistoryDecision,
        },
    },
    training::{canonical_term_hash, DecisionRecord},
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
                // construct a new term by instantiating variables in the pattern ast with terms
                // from the substitution.
                let mut memo = HashMap::default();
                let mut slot_index = 0;
                let mut decisions = Vec::new();
                let mut selection_history = Vec::new();
                let mut used_derived_candidate = false;
                let mut ctx = DecisionLogContext {
                    decisions: &mut decisions,
                    selection_history_decisions: &mut selection_history,
                    record_decisions: self.artifact_capture.decisions,
                    axiom_name: rule.name(),
                    rule_category: rule.category(),
                    slot_index: &mut slot_index,
                    used_derived_candidate: &mut used_derived_candidate,
                };
                let new_lhs: egg::RecExpr<_> = unpatternify(reify_pattern_ast(
                    searcher_ast,
                    egraph,
                    Some(m.eclass),
                    subst,
                    &self.extractor,
                    &mut memo,
                    &mut ctx,
                ));

                let new_rhs: egg::RecExpr<_> = unpatternify(reify_pattern_ast(
                    consequence_ast,
                    egraph,
                    None,
                    subst,
                    &self.extractor,
                    &mut memo,
                    &mut ctx,
                ));

                if self.extractor.requires_source_grounded_candidates()
                    && *ctx.used_derived_candidate
                {
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
                    let instantiation = unpatternify(reify_pattern_ast(
                        executable_rule.formula(),
                        egraph,
                        None,
                        subst,
                        &self.extractor,
                        &mut memo,
                        &mut ctx,
                    ));

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
                    let mut substitution = memo
                        .iter()
                        .map(|(variable, expression)| {
                            (
                                variable.to_string(),
                                expr_to_term(unpatternify(expression.clone())),
                            )
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

struct DecisionLogContext<'a> {
    decisions: &'a mut Vec<DecisionRecord>,
    selection_history_decisions: &'a mut Vec<SelectionHistoryDecision>,
    record_decisions: bool,
    axiom_name: &'a str,
    rule_category: crate::quantified_rule::QuantifiedRuleCategory,
    slot_index: &'a mut u32,
    used_derived_candidate: &'a mut bool,
}

impl DecisionLogContext<'_> {
    fn record_choice<N, CF>(
        &mut self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
        extractor: &ArrayTermExtractor<CF>,
        chosen_term: &ArrayExpr,
    ) where
        N: egg::Analysis<ArrayLanguage>,
        CF: YardbirdCostFunction<ArrayLanguage>,
    {
        if extractor.candidate_origin(egraph, eclass, chosen_term) == CandidateOrigin::Derived {
            *self.used_derived_candidate = true;
        }
        let chosen_hash = canonical_term_hash(chosen_term);
        let decision_key = extractor.decision_key(self.axiom_name, *self.slot_index, eclass);
        self.selection_history_decisions
            .push(SelectionHistoryDecision {
                decision_key: decision_key.clone(),
                chosen_term_hash: chosen_hash.clone(),
            });
        if self.record_decisions {
            self.decisions.push(extractor.decision_record(
                egraph,
                eclass,
                self.axiom_name,
                *self.slot_index,
                chosen_term,
                decision_key,
            ));
        }
        *self.slot_index += 1;
    }
}

/// We want to replace all the variables in the pattern with terms extracted from
/// the egraph. We do this by calling `join_recexprs` on the root of the pattern
/// ast. For enodes, we want to just return them as is. However, we have to build it
/// fresh, so that the ids work out correctly. For patterns, we call
/// `find_best_variable_substitution` which uses egraph extraction to find the best
/// term.
fn reify_pattern_ast<N, CF>(
    pattern: &egg::PatternAst<ArrayLanguage>,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    expected_eclass: Option<egg::Id>,
    subst: &egg::Subst,
    extractor: &ArrayTermExtractor<CF>,
    memo: &mut HashMap<egg::Var, egg::PatternAst<ArrayLanguage>>,
    ctx: &mut DecisionLogContext<'_>,
) -> egg::PatternAst<ArrayLanguage>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    if expected_eclass.is_some() {
        if let Some(expr) = reify_expected_write(
            pattern,
            egraph,
            expected_eclass,
            subst,
            extractor,
            memo,
            ctx,
        ) {
            return expr;
        }
        if let Some(expr) = reify_expected_read(
            pattern,
            egraph,
            expected_eclass,
            subst,
            extractor,
            memo,
            ctx,
        ) {
            return expr;
        }
    }

    match pattern.as_ref() {
        [node] => match node {
            x @ egg::ENodeOrVar::ENode(_) => vec![x.clone()].into(),
            egg::ENodeOrVar::Var(var) => {
                if let Some(expr) = memo.get(var) {
                    expr.clone()
                } else {
                    let eclass = &egraph[expected_eclass.unwrap_or(*subst.get(*var).unwrap())];
                    let expr = find_best_variable_substitution(egraph, eclass, extractor, ctx);
                    memo.insert(*var, expr.clone());
                    expr
                }
            }
        },
        _ => pattern
            .rooted()
            .clone()
            .join_recexprs(|id| match pattern[id].clone() {
                x @ egg::ENodeOrVar::ENode(_) => {
                    if x.is_leaf() {
                        vec![x].into()
                    } else {
                        reify_pattern_ast(
                            &x.build_recexpr(|id| pattern[id].clone()),
                            egraph,
                            None,
                            subst,
                            extractor,
                            memo,
                            ctx,
                        )
                    }
                }
                egg::ENodeOrVar::Var(var) => {
                    if let Some(expr) = memo.get(&var) {
                        expr.clone()
                    } else {
                        let eclass = &egraph[*subst.get(var).unwrap()];
                        let expr = find_best_variable_substitution(egraph, eclass, extractor, ctx);
                        memo.insert(var, expr.clone());
                        expr
                    }
                }
            }),
    }
}

fn reify_expected_write<N, CF>(
    pattern: &egg::PatternAst<ArrayLanguage>,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    expected_eclass: Option<egg::Id>,
    subst: &egg::Subst,
    extractor: &ArrayTermExtractor<CF>,
    memo: &mut HashMap<egg::Var, egg::PatternAst<ArrayLanguage>>,
    ctx: &mut DecisionLogContext<'_>,
) -> Option<egg::PatternAst<ArrayLanguage>>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    let expected_eclass = expected_eclass?;
    let egg::ENodeOrVar::ENode(ArrayLanguage::WriteTyped(
        [index_sort, value_sort, array, index, value],
    )) = pattern.rooted().clone()
    else {
        return None;
    };

    let index_sort = pattern_sort_symbol(pattern, index_sort)?;
    let value_sort = pattern_sort_symbol(pattern, value_sort)?;
    let array_pattern = subpattern(pattern, array);
    let index_pattern = subpattern(pattern, index);
    let value_pattern = subpattern(pattern, value);

    choose_best_expected_candidate(
        extractor,
        memo,
        ctx,
        egraph[expected_eclass]
            .nodes
            .iter()
            .filter_map(|node| match node {
                ArrayLanguage::WriteTyped([_, _, array_id, index_id, value_id]) => {
                    let candidate = (*array_id, *index_id, Some(*value_id));
                    child_patterns_compatible(
                        egraph,
                        subst,
                        [&array_pattern, &index_pattern, &value_pattern],
                        [candidate.0, candidate.1, candidate.2.unwrap()],
                    )
                    .then_some(candidate)
                }
                _ => None,
            }),
        |candidate, candidate_memo, candidate_ctx| {
            let array_expr = unpatternify(reify_pattern_ast(
                &array_pattern,
                egraph,
                Some(candidate.0),
                subst,
                extractor,
                candidate_memo,
                candidate_ctx,
            ));
            let exact_children = best_matching_write_children(
                egraph,
                extractor,
                &array_expr,
                index_sort.as_str(),
                value_sort.as_str(),
                candidate.1,
                candidate.2.unwrap(),
            );
            let index_expr = if let Some((index_expr, _)) = exact_children.as_ref() {
                if is_single_variable_pattern(&index_pattern) {
                    unpatternify(reify_exact_variable_substitution(
                        &index_pattern,
                        candidate.1,
                        index_expr,
                        egraph,
                        extractor,
                        candidate_memo,
                        candidate_ctx,
                    ))
                } else {
                    unpatternify(reify_pattern_ast(
                        &index_pattern,
                        egraph,
                        Some(candidate.1),
                        subst,
                        extractor,
                        candidate_memo,
                        candidate_ctx,
                    ))
                }
            } else {
                unpatternify(reify_pattern_ast(
                    &index_pattern,
                    egraph,
                    Some(candidate.1),
                    subst,
                    extractor,
                    candidate_memo,
                    candidate_ctx,
                ))
            };
            let value_expr = if let Some((_, value_expr)) = exact_children.as_ref() {
                if is_single_variable_pattern(&value_pattern) {
                    unpatternify(reify_exact_variable_substitution(
                        &value_pattern,
                        candidate.2.unwrap(),
                        value_expr,
                        egraph,
                        extractor,
                        candidate_memo,
                        candidate_ctx,
                    ))
                } else {
                    unpatternify(reify_pattern_ast(
                        &value_pattern,
                        egraph,
                        candidate.2,
                        subst,
                        extractor,
                        candidate_memo,
                        candidate_ctx,
                    ))
                }
            } else {
                unpatternify(reify_pattern_ast(
                    &value_pattern,
                    egraph,
                    candidate.2,
                    subst,
                    extractor,
                    candidate_memo,
                    candidate_ctx,
                ))
            };

            let write = ArrayLanguage::write_typed(
                index_sort.as_str(),
                value_sort.as_str(),
                array_expr,
                index_expr,
                value_expr,
            );
            if !extractor.is_source_write(&write) {
                *candidate_ctx.used_derived_candidate = true;
            }
            write
        },
    )
}

fn reify_expected_read<N, CF>(
    pattern: &egg::PatternAst<ArrayLanguage>,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    expected_eclass: Option<egg::Id>,
    subst: &egg::Subst,
    extractor: &ArrayTermExtractor<CF>,
    memo: &mut HashMap<egg::Var, egg::PatternAst<ArrayLanguage>>,
    ctx: &mut DecisionLogContext<'_>,
) -> Option<egg::PatternAst<ArrayLanguage>>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    let expected_eclass = expected_eclass?;
    let egg::ENodeOrVar::ENode(ArrayLanguage::ReadTyped([index_sort, value_sort, array, index])) =
        pattern.rooted().clone()
    else {
        return None;
    };

    let index_sort = pattern_sort_symbol(pattern, index_sort)?;
    let value_sort = pattern_sort_symbol(pattern, value_sort)?;
    let array_pattern = subpattern(pattern, array);
    let index_pattern = subpattern(pattern, index);

    choose_best_expected_candidate(
        extractor,
        memo,
        ctx,
        egraph[expected_eclass]
            .nodes
            .iter()
            .filter_map(|node| match node {
                ArrayLanguage::ReadTyped([_, _, array_id, index_id]) => {
                    let candidate = (*array_id, *index_id, None);
                    child_patterns_compatible(
                        egraph,
                        subst,
                        [&array_pattern, &index_pattern],
                        [candidate.0, candidate.1],
                    )
                    .then_some(candidate)
                }
                _ => None,
            }),
        |candidate, candidate_memo, candidate_ctx| {
            let array_expr = unpatternify(reify_pattern_ast(
                &array_pattern,
                egraph,
                Some(candidate.0),
                subst,
                extractor,
                candidate_memo,
                candidate_ctx,
            ));
            let index_expr = unpatternify(reify_pattern_ast(
                &index_pattern,
                egraph,
                Some(candidate.1),
                subst,
                extractor,
                candidate_memo,
                candidate_ctx,
            ));

            ArrayLanguage::read_typed(
                index_sort.as_str(),
                value_sort.as_str(),
                array_expr,
                index_expr,
            )
        },
    )
}

fn choose_best_expected_candidate<CF, I, F>(
    extractor: &ArrayTermExtractor<CF>,
    memo: &mut HashMap<egg::Var, egg::PatternAst<ArrayLanguage>>,
    ctx: &mut DecisionLogContext<'_>,
    candidates: I,
    build_expr: F,
) -> Option<egg::PatternAst<ArrayLanguage>>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
    I: IntoIterator<Item = (egg::Id, egg::Id, Option<egg::Id>)>,
    F: Fn(
        (egg::Id, egg::Id, Option<egg::Id>),
        &mut HashMap<egg::Var, egg::PatternAst<ArrayLanguage>>,
        &mut DecisionLogContext<'_>,
    ) -> ArrayExpr,
{
    type ExpectedCandidate = (
        u32,
        String,
        egg::PatternAst<ArrayLanguage>,
        HashMap<egg::Var, egg::PatternAst<ArrayLanguage>>,
        Vec<DecisionRecord>,
        Vec<SelectionHistoryDecision>,
        u32,
        bool,
    );

    let mut best: Option<ExpectedCandidate> = None;

    for candidate in candidates {
        let mut candidate_memo = memo.clone();
        let mut candidate_decisions = Vec::new();
        let mut candidate_selection_history_decisions = Vec::new();
        let mut candidate_slot_index = *ctx.slot_index;
        let mut candidate_used_derived = *ctx.used_derived_candidate;
        let expr = build_expr(
            candidate,
            &mut candidate_memo,
            &mut DecisionLogContext {
                decisions: &mut candidate_decisions,
                selection_history_decisions: &mut candidate_selection_history_decisions,
                record_decisions: ctx.record_decisions,
                axiom_name: ctx.axiom_name,
                rule_category: ctx.rule_category,
                slot_index: &mut candidate_slot_index,
                used_derived_candidate: &mut candidate_used_derived,
            },
        );

        let cost = extractor.cost_of_at("expected_read_write_candidate", &expr);
        let rendered = expr.to_string();
        let should_replace = best.as_ref().is_none_or(
            |(best_cost, best_rendered, _, _, _, _, _, best_used_derived)| {
                if extractor.prefers_source_on_cost_tie() {
                    (cost, candidate_used_derived, rendered.as_str())
                        < (*best_cost, *best_used_derived, best_rendered.as_str())
                } else {
                    (cost, rendered.as_str()) < (*best_cost, best_rendered.as_str())
                }
            },
        );

        if should_replace {
            best = Some((
                cost,
                rendered,
                patternify(&expr),
                candidate_memo,
                candidate_decisions,
                candidate_selection_history_decisions,
                candidate_slot_index,
                candidate_used_derived,
            ));
        }
    }

    let (
        _,
        _,
        chosen_pattern,
        chosen_memo,
        chosen_decisions,
        chosen_selection_history_decisions,
        chosen_slot_index,
        chosen_used_derived,
    ) = best?;
    *memo = chosen_memo;
    ctx.decisions.extend(chosen_decisions);
    ctx.selection_history_decisions
        .extend(chosen_selection_history_decisions);
    *ctx.slot_index = chosen_slot_index;
    *ctx.used_derived_candidate = chosen_used_derived;
    Some(chosen_pattern)
}

fn subpattern(
    pattern: &egg::PatternAst<ArrayLanguage>,
    root: egg::Id,
) -> egg::PatternAst<ArrayLanguage> {
    let node = pattern[root].clone();
    if node.is_leaf() {
        vec![node].into()
    } else {
        node.build_recexpr(|id| pattern[id].clone())
    }
}

fn pattern_sort_symbol(pattern: &egg::PatternAst<ArrayLanguage>, id: egg::Id) -> Option<String> {
    match &pattern[id] {
        egg::ENodeOrVar::ENode(ArrayLanguage::Symbol(symbol)) => Some(symbol.to_string()),
        _ => None,
    }
}

fn patternify(expr: &ArrayExpr) -> egg::PatternAst<ArrayLanguage> {
    expr.as_ref()
        .iter()
        .cloned()
        .map(egg::ENodeOrVar::ENode)
        .collect::<Vec<_>>()
        .into()
}

fn best_matching_write_children<N, CF>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    extractor: &ArrayTermExtractor<CF>,
    array_expr: &ArrayExpr,
    index_sort: &str,
    value_sort: &str,
    index_eclass: egg::Id,
    value_eclass: egg::Id,
) -> Option<(ArrayExpr, ArrayExpr)>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    let index_eclass = egraph.find(index_eclass);
    let value_eclass = egraph.find(value_eclass);
    if let Some(cached) = extractor.cached_matching_write(
        array_expr,
        index_sort,
        value_sort,
        index_eclass,
        value_eclass,
    ) {
        return cached;
    }

    let best_in_pool = |candidates: &[(ArrayExpr, ArrayExpr)]| {
        let mut best: Option<(u32, String, ArrayExpr, ArrayExpr)> = None;
        for (index_expr, value_expr) in candidates {
            if !egraph_contains_at(egraph, index_expr, index_eclass) {
                continue;
            }
            if !egraph_contains_at(egraph, value_expr, value_eclass) {
                continue;
            }

            let write_expr = ArrayLanguage::write_typed(
                index_sort,
                value_sort,
                array_expr.clone(),
                index_expr.clone(),
                value_expr.clone(),
            );
            let cost = extractor.cost_of_at("best_matching_write_child", &write_expr);
            let rendered = write_expr.to_string();
            let should_replace = best
                .as_ref()
                .is_none_or(|(best_cost, best_rendered, _, _)| {
                    (cost, rendered.as_str()) < (*best_cost, best_rendered.as_str())
                });
            if should_replace {
                best = Some((cost, rendered, index_expr.clone(), value_expr.clone()));
            }
        }
        best
    };

    let best = if extractor.prefers_source_on_cost_tie() {
        best_in_pool(extractor.source_write_candidates(array_expr))
    } else {
        best_in_pool(extractor.all_write_candidates(array_expr))
    };
    let result = best.map(|(_, _, index_expr, value_expr)| (index_expr, value_expr));
    extractor.cache_matching_write(
        array_expr,
        index_sort,
        value_sort,
        index_eclass,
        value_eclass,
        result.clone(),
    );
    result
}

fn reify_exact_variable_substitution<N, CF>(
    pattern: &egg::PatternAst<ArrayLanguage>,
    eclass: egg::Id,
    expr: &ArrayExpr,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    extractor: &ArrayTermExtractor<CF>,
    memo: &mut HashMap<egg::Var, egg::PatternAst<ArrayLanguage>>,
    ctx: &mut DecisionLogContext<'_>,
) -> egg::PatternAst<ArrayLanguage>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    match pattern.as_ref() {
        [egg::ENodeOrVar::Var(var)] => {
            if let Some(existing) = memo.get(var) {
                return existing.clone();
            }

            if trace_conflicts_enabled() {
                trace_conflicts(format!(
                    "      choice slot={} axiom={} eclass={} expr={}",
                    *ctx.slot_index, ctx.axiom_name, eclass, expr
                ));
            }
            ctx.record_choice(egraph, eclass, extractor, expr);

            let pattern_expr = patternify(expr);
            memo.insert(*var, pattern_expr.clone());
            pattern_expr
        }
        _ => unreachable!("exact substitutions are only used for variable patterns"),
    }
}

fn is_single_variable_pattern(pattern: &egg::PatternAst<ArrayLanguage>) -> bool {
    matches!(pattern.as_ref(), [egg::ENodeOrVar::Var(_)])
}

fn egraph_contains_at<N>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    expr: &ArrayExpr,
    expected_eclass: egg::Id,
) -> bool
where
    N: egg::Analysis<ArrayLanguage>,
{
    egraph
        .lookup_expr(expr)
        .is_some_and(|actual| egraph.find(actual) == egraph.find(expected_eclass))
}

fn child_patterns_compatible<const N_CHILDREN: usize, N>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    subst: &egg::Subst,
    patterns: [&egg::PatternAst<ArrayLanguage>; N_CHILDREN],
    candidate_eclasses: [egg::Id; N_CHILDREN],
) -> bool
where
    N: egg::Analysis<ArrayLanguage>,
{
    patterns
        .into_iter()
        .zip(candidate_eclasses)
        .all(|(pattern, candidate_eclass)| {
            pattern_matches_eclass(pattern, candidate_eclass, egraph, subst)
        })
}

fn pattern_matches_eclass<N>(
    pattern: &egg::PatternAst<ArrayLanguage>,
    candidate_eclass: egg::Id,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    subst: &egg::Subst,
) -> bool
where
    N: egg::Analysis<ArrayLanguage>,
{
    match pattern.rooted() {
        egg::ENodeOrVar::Var(var) => {
            egraph.find(candidate_eclass) == egraph.find(*subst.get(*var).unwrap())
        }
        egg::ENodeOrVar::ENode(pattern_node) => egraph[candidate_eclass].nodes.iter().any(|node| {
            pattern_node.matches(node)
                && pattern_node.children().iter().zip(node.children()).all(
                    |(pattern_child, candidate_child)| {
                        pattern_matches_eclass(
                            &subpattern(pattern, *pattern_child),
                            *candidate_child,
                            egraph,
                            subst,
                        )
                    },
                )
        }),
    }
}

fn unpatternify(pattern: egg::PatternAst<ArrayLanguage>) -> egg::RecExpr<ArrayLanguage> {
    pattern
        .as_ref()
        .iter()
        .map(|node| match node {
            egg::ENodeOrVar::ENode(node) => node.clone(),
            egg::ENodeOrVar::Var(_) => panic!("Can't unpatternify vars"),
        })
        .collect::<Vec<_>>()
        .into()
}

fn find_best_variable_substitution<N, CF>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    eclass: &egg::EClass<ArrayLanguage, <N as Analysis<ArrayLanguage>>::Data>,
    extractor: &ArrayTermExtractor<CF>,
    ctx: &mut DecisionLogContext<'_>,
) -> egg::PatternAst<ArrayLanguage>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    let expr = extractor.extract_for_decision(
        egraph,
        eclass.id,
        ctx.axiom_name,
        ctx.rule_category,
        *ctx.slot_index,
    );
    if trace_conflicts_enabled() {
        trace_conflicts(format!(
            "      choice slot={} axiom={} eclass={} expr={}",
            *ctx.slot_index, ctx.axiom_name, eclass.id, expr
        ));
    }
    debug!("    extraction: {} -> {}", eclass.id, expr.pretty(80));
    ctx.record_choice(egraph, eclass.id, extractor, &expr);

    // wrap everything in an ENodeOrVar so that it still counts as an egg::PatternAst
    expr.as_ref()
        .iter()
        .cloned()
        .map(egg::ENodeOrVar::ENode)
        .collect::<Vec<_>>()
        .into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        cost_functions::YardbirdCostFunction,
        problem_context::{ArrayCandidateCatalog, ArrayCandidatePool},
        theories::array::{
            array_term_extractor::ArrayTermExtractorOptions, candidate_scope::CandidateScope,
        },
    };
    use rustc_hash::FxHashMap;
    use smt2parser::vmt::ReadsAndWrites;

    #[derive(Clone)]
    struct ZeroCost;

    impl egg::CostFunction<ArrayLanguage> for ZeroCost {
        type Cost = u32;

        fn cost<C>(&mut self, _enode: &ArrayLanguage, _costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            0
        }
    }

    impl YardbirdCostFunction<ArrayLanguage> for ZeroCost {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }
    }

    #[test]
    fn source_only_lookup_returns_the_exact_source_write_children() {
        let write: ArrayExpr = "(Write Int Int A i v)".parse().unwrap();
        let array: ArrayExpr = "A".parse().unwrap();
        let index: ArrayExpr = "i".parse().unwrap();
        let value: ArrayExpr = "v".parse().unwrap();
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&write);
        egraph.rebuild();
        let index_eclass = egraph.lookup_expr(&index).unwrap();
        let value_eclass = egraph.lookup_expr(&value).unwrap();
        let source_reads_and_writes = ReadsAndWrites::from(
            std::collections::HashSet::new(),
            std::collections::HashSet::from([("A".to_string(), "i".to_string(), "v".to_string())]),
        );
        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCost,
            ArrayTermExtractorOptions {
                candidate_catalog: ArrayCandidateCatalog {
                    source_grounded: ArrayCandidatePool {
                        terms: vec![
                            "A".to_string(),
                            "i".to_string(),
                            "v".to_string(),
                            "(Write_Int_Int A i v)".to_string(),
                        ],
                        reads_and_writes: source_reads_and_writes,
                    },
                    derived: ArrayCandidatePool::default(),
                },
                candidate_scope: CandidateScope::SourceGroundedOnly,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                profiling: None,
            },
        );

        assert_eq!(
            best_matching_write_children(
                &egraph,
                &extractor,
                &array,
                "Int",
                "Int",
                index_eclass,
                value_eclass,
            ),
            Some((index, value))
        );
    }

    #[test]
    fn source_write_lookup_canonicalizes_nested_array_lineage() {
        let array: ArrayExpr = "(Write Int Int A outer previous)".parse().unwrap();
        let index: ArrayExpr = "i".parse().unwrap();
        let value: ArrayExpr = "v".parse().unwrap();
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&array);
        let index_eclass = egraph.add_expr(&index);
        let value_eclass = egraph.add_expr(&value);
        egraph.rebuild();
        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCost,
            ArrayTermExtractorOptions {
                candidate_catalog: ArrayCandidateCatalog {
                    source_grounded: ArrayCandidatePool {
                        terms: vec![],
                        reads_and_writes: ReadsAndWrites::from(
                            std::collections::HashSet::new(),
                            std::collections::HashSet::from([(
                                "(Write_Int_Int A outer previous)".into(),
                                "i".into(),
                                "v".into(),
                            )]),
                        ),
                    },
                    derived: ArrayCandidatePool::default(),
                },
                candidate_scope: CandidateScope::SourceGroundedOnly,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                profiling: None,
            },
        );

        assert_eq!(
            best_matching_write_children(
                &egraph,
                &extractor,
                &array,
                "Int",
                "Int",
                index_eclass,
                value_eclass,
            ),
            Some((index, value))
        );
    }
}
