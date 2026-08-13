use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
    time::Instant,
};

use egg::{Analysis, Language};
use log::{debug, trace};

use crate::{
    auxiliary_synthesis::{ArrayConflictRecord, ConflictClassification},
    cost_functions::YardbirdCostFunction,
    egg_utils::RecExprRoot,
    profiling::ArrayProfilingCollector,
    theories::array::{
        array_axioms::{expr_to_term, ArrayExpr, ArrayLanguage},
        array_term_extractor::{ArrayTermExtractor, CandidateOrigin},
    },
    training::{canonical_term_hash, AbstractInstantiationRecord, DecisionRecord},
};

fn trace_conflicts_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

fn trace_conflicts(message: impl AsRef<str>) {
    trace!("[yardbird::conflict-trace] {}", message.as_ref());
}

fn is_write_does_not_overwrite_axiom(name: &str) -> bool {
    name == "write-does-not-overwrite" || name.starts_with("write-does-not-overwrite-")
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ArrayArtifactCapture {
    pub decisions: bool,
    pub instantiation_provenance: bool,
    pub conflicts: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct SelectionHistoryDecision {
    pub decision_key: String,
    pub chosen_term_hash: String,
}

type InstantiationDecisionLog = Rc<RefCell<Vec<(ArrayExpr, Vec<String>)>>>;

pub struct ArrayConflictSchedulerOptions {
    pub excluded_instantiations: HashSet<ArrayExpr>,
    pub refinement_step: u32,
    pub depth: u16,
    pub artifact_capture: ArrayArtifactCapture,
    pub profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

/// Preprocess array operation strings for egg parsing.
/// Converts: "(Read_Int_Int a b)" -> "(Read Int Int a b)"
/// Handles nested arrays: "(Read_Int_Array_Int_Int a b)" -> "(Read Int Array_Int_Int a b)"
pub fn preprocess_array_expr(input: &str) -> String {
    let mut result = String::with_capacity(input.len() + 10);
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '(' {
            result.push(ch);

            // Check if next tokens form an array operation
            let mut op_name = String::new();

            // Collect operator name (before first space or closing paren)
            while let Some(&next_ch) = chars.peek() {
                if next_ch.is_whitespace() || next_ch == ')' {
                    break;
                }
                op_name.push(chars.next().unwrap());
            }

            // Check if it's a typed array operation
            if let Some(rest) = op_name.strip_prefix("Read_") {
                // Split on first two underscores: Read_IndexSort_ValueSort
                let parts: Vec<&str> = rest.splitn(2, '_').collect();
                if parts.len() == 2 {
                    result.push_str("Read ");
                    result.push_str(parts[0]);
                    result.push(' ');
                    result.push_str(parts[1]);
                } else {
                    result.push_str(&op_name);
                }
            } else if let Some(rest) = op_name.strip_prefix("Write_") {
                let parts: Vec<&str> = rest.splitn(2, '_').collect();
                if parts.len() == 2 {
                    result.push_str("Write ");
                    result.push_str(parts[0]);
                    result.push(' ');
                    result.push_str(parts[1]);
                } else {
                    result.push_str(&op_name);
                }
            } else if let Some(rest) = op_name.strip_prefix("ConstArr_") {
                let parts: Vec<&str> = rest.splitn(2, '_').collect();
                if parts.len() == 2 {
                    result.push_str("ConstArr ");
                    result.push_str(parts[0]);
                    result.push(' ');
                    result.push_str(parts[1]);
                } else {
                    result.push_str(&op_name);
                }
            } else {
                // Not an array operation, keep as-is
                result.push_str(&op_name);
            }
        } else {
            result.push(ch);
        }
    }

    result
}

pub struct ArrayConflictScheduler<S, CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    inner: S,
    /// TODO: use RecExpr instead of String
    /// Keep track of rule instantiations that caused conflicts. We use an
    /// `Rc<RefCell<...>>` here because the scheduler isn't public on `egg::Runner`. So
    /// in order to be able to get data out of the scheduler after a saturation run, we
    /// need to use interior mutability.
    instantiations: Rc<RefCell<Vec<ArrayExpr>>>,
    instantiations_w_constants: Rc<RefCell<Vec<ArrayExpr>>>,
    conflicts: Rc<RefCell<Vec<ArrayConflictRecord>>>,
    decisions: Rc<RefCell<Vec<DecisionRecord>>>,
    abstract_instantiations: Rc<RefCell<Vec<AbstractInstantiationRecord>>>,
    selection_history_decisions: Rc<RefCell<Vec<SelectionHistoryDecision>>>,
    instantiation_decision_keys: InstantiationDecisionLog,
    artifact_capture: ArrayArtifactCapture,
    next_instantiation_ordinal: usize,
    pub cost_fn: CF,
    extractor: ArrayTermExtractor<CF>,
    excluded_instantiations: HashSet<ArrayExpr>,
    refinement_step: u32,
    depth: u16,
    profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

impl<S, CF> ArrayConflictScheduler<S, CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    pub fn new(
        scheduler: S,
        cost_fn: CF,
        extractor: ArrayTermExtractor<CF>,
        options: ArrayConflictSchedulerOptions,
    ) -> Self {
        let ArrayConflictSchedulerOptions {
            excluded_instantiations,
            refinement_step,
            depth,
            artifact_capture,
            profiling,
        } = options;
        Self {
            inner: scheduler,
            instantiations: Rc::new(RefCell::new(vec![])),
            instantiations_w_constants: Rc::new(RefCell::new(vec![])),
            conflicts: Rc::new(RefCell::new(vec![])),
            decisions: Rc::new(RefCell::new(vec![])),
            abstract_instantiations: Rc::new(RefCell::new(vec![])),
            selection_history_decisions: Rc::new(RefCell::new(vec![])),
            instantiation_decision_keys: Rc::new(RefCell::new(vec![])),
            artifact_capture,
            next_instantiation_ordinal: 0,
            cost_fn,
            extractor,
            excluded_instantiations,
            refinement_step,
            depth,
            profiling,
        }
    }

    pub fn instantiations(&self) -> Rc<RefCell<Vec<ArrayExpr>>> {
        Rc::clone(&self.instantiations)
    }

    pub fn instantiations_w_constants(&self) -> Rc<RefCell<Vec<ArrayExpr>>> {
        Rc::clone(&self.instantiations_w_constants)
    }

    pub fn conflicts(&self) -> Rc<RefCell<Vec<ArrayConflictRecord>>> {
        Rc::clone(&self.conflicts)
    }

    pub fn decisions(&self) -> Rc<RefCell<Vec<DecisionRecord>>> {
        Rc::clone(&self.decisions)
    }

    pub fn abstract_instantiations(&self) -> Rc<RefCell<Vec<AbstractInstantiationRecord>>> {
        Rc::clone(&self.abstract_instantiations)
    }

    pub(crate) fn selection_history_decisions(&self) -> Rc<RefCell<Vec<SelectionHistoryDecision>>> {
        Rc::clone(&self.selection_history_decisions)
    }

    pub(crate) fn instantiation_decision_keys(&self) -> InstantiationDecisionLog {
        Rc::clone(&self.instantiation_decision_keys)
    }
}

impl<S, N, CF> egg::RewriteScheduler<ArrayLanguage, N> for ArrayConflictScheduler<S, CF>
where
    S: egg::RewriteScheduler<ArrayLanguage, N>,
    CF: YardbirdCostFunction<ArrayLanguage>,
    N: egg::Analysis<ArrayLanguage>,
{
    fn can_stop(&mut self, iteration: usize) -> bool {
        self.inner.can_stop(iteration)
    }

    fn search_rewrite<'a>(
        &mut self,
        iteration: usize,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        rewrite: &'a egg::Rewrite<ArrayLanguage, N>,
    ) -> Vec<egg::SearchMatches<'a, ArrayLanguage>> {
        let search_start = Instant::now();
        let matches = self.inner.search_rewrite(iteration, egraph, rewrite);
        if let Some(profiling) = &self.profiling {
            let substitutions = matches
                .iter()
                .map(|search_match| search_match.substs.len())
                .sum();
            profiling.borrow_mut().record_search_rewrite(
                rewrite.name.as_str(),
                matches.len(),
                substitutions,
                search_start.elapsed(),
            );
        }
        if trace_conflicts_enabled() {
            trace_conflicts(format!(
                "search iteration={iteration} rewrite={} eclasses={} matches={} existing_insts={}",
                rewrite.name,
                egraph.number_of_classes(),
                matches.len(),
                self.instantiations.borrow().len()
            ));
            for (match_ix, search_match) in matches.iter().enumerate() {
                trace_conflicts(format!(
                    "  match[{match_ix}] eclass={} subst_count={} has_ast={}",
                    search_match.eclass,
                    search_match.substs.len(),
                    search_match.ast.is_some()
                ));
            }
        }
        matches
    }

    fn apply_rewrite(
        &mut self,
        iteration: usize,
        egraph: &mut egg::EGraph<ArrayLanguage, N>,
        rewrite: &egg::Rewrite<ArrayLanguage, N>,
        matches: Vec<egg::SearchMatches<ArrayLanguage>>,
    ) -> usize {
        let apply_start = Instant::now();
        let mut substitutions_explored = 0usize;
        let tracing = trace_conflicts_enabled();
        debug!("======>");
        debug!(
            "apply_rewrite: {} with {} matches, inst_count={}",
            rewrite.name,
            matches.len(),
            self.instantiations.borrow().len()
        );
        if tracing {
            trace_conflicts(format!(
                "apply iteration={iteration} rewrite={} matches={} existing_insts={}",
                rewrite.name,
                matches.len(),
                self.instantiations.borrow().len()
            ));
        }
        let explore_all_matches = self.extractor.explores_all_matches();
        if !explore_all_matches && !self.instantiations.borrow().is_empty() {
            if let Some(profiling) = &self.profiling {
                profiling.borrow_mut().record_apply_rewrite(
                    rewrite.name.as_str(),
                    substitutions_explored,
                    true,
                    apply_start.elapsed(),
                );
            }
            return 0;
        }
        'matches: for (match_ix, m) in matches.iter().enumerate() {
            if let Some(searcher_ast) = &m.ast {
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

                    if let Some(applier_ast) = rewrite.applier.get_pattern_ast() {
                        // construct a new term by instantiating variables in the pattern ast with terms
                        // from the substitution.
                        let mut memo = HashMap::default();
                        let mut slot_index = 0;
                        let mut decisions = self.decisions.borrow_mut();
                        let decision_start = decisions.len();
                        let mut selection_history_decisions =
                            self.selection_history_decisions.borrow_mut();
                        let selection_start = selection_history_decisions.len();
                        let mut used_derived_candidate = false;
                        let mut ctx = DecisionLogContext {
                            decisions: &mut decisions,
                            selection_history_decisions: &mut selection_history_decisions,
                            record_decisions: self.artifact_capture.decisions,
                            axiom_name: rewrite.name.as_str(),
                            slot_index: &mut slot_index,
                            used_derived_candidate: &mut used_derived_candidate,
                        };
                        let new_lhs: egg::RecExpr<_> = unpatternify(reify_pattern_ast(
                            searcher_ast.as_ref(),
                            egraph,
                            Some(m.eclass),
                            subst,
                            &self.extractor,
                            &mut memo,
                            &mut ctx,
                        ));

                        let new_rhs: egg::RecExpr<_> = unpatternify(reify_pattern_ast(
                            applier_ast,
                            egraph,
                            None,
                            subst,
                            &self.extractor,
                            &mut memo,
                            &mut ctx,
                        ));

                        if self.extractor.requires_source_grounded_candidates()
                            && used_derived_candidate
                        {
                            decisions.truncate(decision_start);
                            selection_history_decisions.truncate(selection_start);
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
                            let instantiation: ArrayExpr =
                                if is_write_does_not_overwrite_axiom(rewrite.name.as_str()) {
                                    let expr1 = &memo[&"?c".parse::<egg::Var>().unwrap()];
                                    let expr2 = &memo[&"?idx".parse::<egg::Var>().unwrap()];
                                    // construct: (=> (not (= {} {})) (= {} {}))
                                    ArrayLanguage::not_implies(
                                        &ArrayLanguage::equals(
                                            &unpatternify(expr1.clone()),
                                            &unpatternify(expr2.clone()),
                                        ),
                                        &ArrayLanguage::equals(&new_lhs, &new_rhs),
                                    )
                                } else {
                                    ArrayLanguage::equals(&new_lhs, &new_rhs)
                                };
                            if self.excluded_instantiations.contains(&instantiation) {
                                decisions.truncate(decision_start);
                                selection_history_decisions.truncate(selection_start);
                                if tracing {
                                    trace_conflicts(format!(
                                        "    subst[{subst_ix}] skipped because the complete instantiation was excluded"
                                    ));
                                }
                                continue;
                            }
                            let selection_decision_keys = selection_history_decisions
                                [selection_start..]
                                .iter()
                                .map(|decision| decision.decision_key.clone())
                                .collect::<Vec<_>>();
                            self.instantiation_decision_keys
                                .borrow_mut()
                                .push((instantiation.clone(), selection_decision_keys.clone()));
                            let decision_keys = if self.artifact_capture.decisions {
                                selection_decision_keys
                            } else {
                                vec![]
                            };
                            let ordinal = self.next_instantiation_ordinal;
                            self.next_instantiation_ordinal += 1;
                            if self.artifact_capture.instantiation_provenance {
                                let abstract_instantiation =
                                    self.extractor.abstract_instantiation_record(
                                        rewrite.name.as_str(),
                                        ordinal,
                                        &instantiation,
                                        decision_keys.clone(),
                                    );
                                self.abstract_instantiations
                                    .borrow_mut()
                                    .push(abstract_instantiation);
                            }
                            let classification_cost = if let Some(profiling) = &self.profiling {
                                let mut cost_fn = self.cost_fn.clone();
                                profiling.borrow_mut().record_cost(
                                    "conflict_classification",
                                    new_rhs.as_ref().len(),
                                    || cost_fn.cost_rec(&new_rhs),
                                )
                            } else {
                                self.cost_fn.cost_rec(&new_rhs)
                            };
                            let cost = if explore_all_matches {
                                if let Some(profiling) = &self.profiling {
                                    let mut cost_fn = self.cost_fn.clone();
                                    profiling.borrow_mut().record_cost(
                                        "complete_instantiation_ranking",
                                        instantiation.as_ref().len(),
                                        || cost_fn.cost_rec(&instantiation),
                                    )
                                } else {
                                    self.cost_fn.cost_rec(&instantiation)
                                }
                            } else {
                                classification_cost
                            };
                            let classification = if classification_cost >= 100 {
                                ConflictClassification::ConstOrHighCost
                            } else {
                                ConflictClassification::Regular
                            };
                            if let Some(profiling) = &self.profiling {
                                profiling.borrow_mut().record_conflict(
                                    rewrite.name.as_str(),
                                    classification_cost >= 100,
                                );
                            }
                            if self.artifact_capture.conflicts {
                                let conflict_record = ArrayConflictRecord::new(
                                    ordinal,
                                    rewrite.name.as_str(),
                                    instantiation.clone(),
                                    expr_to_term(instantiation.clone()),
                                    self.depth,
                                    self.refinement_step,
                                    cost,
                                    classification,
                                    decision_keys,
                                );
                                self.conflicts.borrow_mut().push(conflict_record);
                            }
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
                            if classification_cost >= 100 {
                                debug!("rejecting because of cost");
                                if tracing {
                                    trace_conflicts(
                                        "    classified as const/high-cost instantiation",
                                    );
                                }
                                self.instantiations_w_constants
                                    .borrow_mut()
                                    .push(instantiation);
                            } else {
                                if tracing {
                                    trace_conflicts("    accepted as regular instantiation");
                                }
                                self.instantiations.borrow_mut().push(instantiation);
                                if !explore_all_matches {
                                    break 'matches;
                                }
                            }
                        } else if tracing {
                            trace_conflicts(format!(
                                "    subst[{subst_ix}] no conflict because rhs already maps to eclass {}",
                                m.eclass
                            ));
                        }
                    }
                }
            }
        }
        debug!("<======");
        if let Some(profiling) = &self.profiling {
            profiling.borrow_mut().record_apply_rewrite(
                rewrite.name.as_str(),
                substitutions_explored,
                false,
                apply_start.elapsed(),
            );
        }
        // we don't actually want to apply the rewrite, because it would be a violation
        0
    }
}

struct DecisionLogContext<'a> {
    decisions: &'a mut Vec<DecisionRecord>,
    selection_history_decisions: &'a mut Vec<SelectionHistoryDecision>,
    record_decisions: bool,
    axiom_name: &'a str,
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
        let source = best_in_pool(extractor.source_write_candidates(array_expr));
        let derived = extractor
            .allows_derived_candidates()
            .then(|| best_in_pool(extractor.derived_write_candidates(array_expr)))
            .flatten();
        match (source, derived) {
            (Some(source), Some(derived)) => {
                if (source.0, false, source.1.as_str()) <= (derived.0, true, derived.1.as_str()) {
                    Some(source)
                } else {
                    Some(derived)
                }
            }
            (source @ Some(_), None) => source,
            (None, derived) => derived,
        }
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
    let expr = extractor.extract_for_decision(egraph, eclass.id, ctx.axiom_name, *ctx.slot_index);
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

    #[derive(Clone)]
    struct PreferDerivedWrite {
        terms: Vec<ArrayExpr>,
    }

    impl egg::CostFunction<ArrayLanguage> for PreferDerivedWrite {
        type Cost = u32;

        fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            let self_cost = match enode {
                ArrayLanguage::Symbol(symbol) if symbol.as_str() == "source_index" => 10,
                _ => 0,
            };
            enode.fold(self_cost, |sum, id| sum.saturating_add(costs(id)))
        }
    }

    impl YardbirdCostFunction<ArrayLanguage> for PreferDerivedWrite {
        fn get_string_terms(&self) -> Vec<String> {
            self.terms.iter().map(ToString::to_string).collect()
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

    #[test]
    fn specialized_write_matching_uses_source_only_as_a_cost_tie_breaker() {
        let array: ArrayExpr = "A".parse().unwrap();
        let source_index: ArrayExpr = "source_index".parse().unwrap();
        let derived_index: ArrayExpr = "derived_index".parse().unwrap();
        let value: ArrayExpr = "v".parse().unwrap();
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        let source_index_id = egraph.add_expr(&source_index);
        let derived_index_id = egraph.add_expr(&derived_index);
        egraph.union(source_index_id, derived_index_id);
        let value_id = egraph.add_expr(&value);
        egraph.rebuild();
        let index_eclass = egraph.find(source_index_id);
        let source_write = ArrayLanguage::write_typed(
            "Int",
            "Int",
            array.clone(),
            source_index.clone(),
            value.clone(),
        );
        let derived_write = ArrayLanguage::write_typed(
            "Int",
            "Int",
            array.clone(),
            derived_index.clone(),
            value.clone(),
        );
        let extractor = ArrayTermExtractor::new(
            &egraph,
            PreferDerivedWrite {
                terms: vec![
                    array.clone(),
                    source_index.clone(),
                    derived_index.clone(),
                    value.clone(),
                    source_write,
                    derived_write,
                ],
            },
            ArrayTermExtractorOptions {
                candidate_catalog: ArrayCandidateCatalog {
                    source_grounded: ArrayCandidatePool {
                        terms: vec!["A".into(), "source_index".into(), "v".into()],
                        reads_and_writes: ReadsAndWrites::from(
                            std::collections::HashSet::new(),
                            std::collections::HashSet::from([(
                                "A".into(),
                                "source_index".into(),
                                "v".into(),
                            )]),
                        ),
                    },
                    derived: ArrayCandidatePool {
                        terms: vec!["derived_index".into()],
                        reads_and_writes: ReadsAndWrites::from(
                            std::collections::HashSet::new(),
                            std::collections::HashSet::from([(
                                "A".into(),
                                "derived_index".into(),
                                "v".into(),
                            )]),
                        ),
                    },
                },
                candidate_scope: CandidateScope::SourceThenDerived,
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
                value_id,
            ),
            Some((derived_index, value))
        );
    }
}
