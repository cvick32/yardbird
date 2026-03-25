use std::{cell::RefCell, collections::HashMap, rc::Rc};

use egg::{Analysis, Language};
use log::{debug, trace};

use crate::{
    cost_functions::YardbirdCostFunction,
    egg_utils::RecExprRoot,
    theories::array::{
        array_axioms::{ArrayExpr, ArrayLanguage},
        array_term_extractor::ArrayTermExtractor,
    },
    training::{AbstractInstantiationRecord, DecisionRecord},
};

fn trace_conflicts_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

fn trace_conflicts(message: impl AsRef<str>) {
    trace!("[yardbird::conflict-trace] {}", message.as_ref());
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
    decisions: Rc<RefCell<Vec<DecisionRecord>>>,
    abstract_instantiations: Rc<RefCell<Vec<AbstractInstantiationRecord>>>,
    pub cost_fn: CF,
    extractor: ArrayTermExtractor<CF>,
}

impl<S, CF> ArrayConflictScheduler<S, CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    pub fn new(scheduler: S, cost_fn: CF, extractor: ArrayTermExtractor<CF>) -> Self {
        Self {
            inner: scheduler,
            instantiations: Rc::new(RefCell::new(vec![])),
            instantiations_w_constants: Rc::new(RefCell::new(vec![])),
            decisions: Rc::new(RefCell::new(vec![])),
            abstract_instantiations: Rc::new(RefCell::new(vec![])),
            cost_fn,
            extractor,
        }
    }

    pub fn instantiations(&self) -> Rc<RefCell<Vec<ArrayExpr>>> {
        Rc::clone(&self.instantiations)
    }

    pub fn instantiations_w_constants(&self) -> Rc<RefCell<Vec<ArrayExpr>>> {
        Rc::clone(&self.instantiations_w_constants)
    }

    pub fn decisions(&self) -> Rc<RefCell<Vec<DecisionRecord>>> {
        Rc::clone(&self.decisions)
    }

    pub fn abstract_instantiations(&self) -> Rc<RefCell<Vec<AbstractInstantiationRecord>>> {
        Rc::clone(&self.abstract_instantiations)
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
        let matches = self.inner.search_rewrite(iteration, egraph, rewrite);
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
        if !self.instantiations.borrow().is_empty() {
            // don't try to keep applying rewrites if we've found an inst
            if tracing {
                trace_conflicts("  skipping because a regular instantiation already exists");
            }
            return 0;
        }
        for (match_ix, m) in matches.iter().enumerate() {
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
                        let mut ctx = DecisionLogContext {
                            decisions: &mut decisions,
                            axiom_name: rewrite.name.as_str(),
                            slot_index: &mut slot_index,
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
                                if rewrite.name.as_str() == "write-does-not-overwrite" {
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
                            let decision_keys = decisions[decision_start..]
                                .iter()
                                .map(|decision| decision.decision_key.clone())
                                .collect::<Vec<_>>();
                            let ordinal = self.abstract_instantiations.borrow().len();
                            let abstract_instantiation =
                                self.extractor.abstract_instantiation_record(
                                    rewrite.name.as_str(),
                                    ordinal,
                                    &instantiation,
                                    decision_keys,
                                );
                            let cost = self.cost_fn.cost_rec(&new_rhs);
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
                            self.abstract_instantiations
                                .borrow_mut()
                                .push(abstract_instantiation);

                            if cost >= 100 {
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
        // we don't actually want to apply the rewrite, because it would be a violation
        0
    }
}

struct DecisionLogContext<'a> {
    decisions: &'a mut Vec<DecisionRecord>,
    axiom_name: &'a str,
    slot_index: &'a mut u32,
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

            ArrayLanguage::write_typed(
                index_sort.as_str(),
                value_sort.as_str(),
                array_expr,
                index_expr,
                value_expr,
            )
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
        u32,
    );

    let mut best: Option<ExpectedCandidate> = None;

    for candidate in candidates {
        let mut candidate_memo = memo.clone();
        let mut candidate_decisions = Vec::new();
        let mut candidate_slot_index = *ctx.slot_index;
        let expr = build_expr(
            candidate,
            &mut candidate_memo,
            &mut DecisionLogContext {
                decisions: &mut candidate_decisions,
                axiom_name: ctx.axiom_name,
                slot_index: &mut candidate_slot_index,
            },
        );

        let cost = extractor.cost_of(&expr);
        let rendered = expr.to_string();
        let should_replace = best
            .as_ref()
            .is_none_or(|(best_cost, best_rendered, _, _, _, _)| {
                (cost, rendered.as_str()) < (*best_cost, best_rendered.as_str())
            });

        if should_replace {
            best = Some((
                cost,
                rendered,
                patternify(&expr),
                candidate_memo,
                candidate_decisions,
                candidate_slot_index,
            ));
        }
    }

    let (_, _, chosen_pattern, chosen_memo, chosen_decisions, chosen_slot_index) = best?;
    *memo = chosen_memo;
    ctx.decisions.extend(chosen_decisions);
    *ctx.slot_index = chosen_slot_index;
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
    let mut best: Option<(u32, String, ArrayExpr, ArrayExpr)> = None;

    for raw_index in extractor.reads_and_writes.write_array(array_expr) {
        let Ok(index_expr) = preprocess_array_expr(&raw_index).parse::<ArrayExpr>() else {
            continue;
        };
        if !egraph_contains_at(egraph, &index_expr, index_eclass) {
            continue;
        }

        for raw_value in extractor
            .reads_and_writes
            .write_array_index(array_expr, &index_expr)
        {
            let Ok(value_expr) = preprocess_array_expr(&raw_value).parse::<ArrayExpr>() else {
                continue;
            };
            if !egraph_contains_at(egraph, &value_expr, value_eclass) {
                continue;
            }

            let write_expr = ArrayLanguage::write_typed(
                index_sort,
                value_sort,
                array_expr.clone(),
                index_expr.clone(),
                value_expr.clone(),
            );
            let cost = extractor.cost_of(&write_expr);
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
    }

    best.map(|(_, _, index_expr, value_expr)| (index_expr, value_expr))
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
            ctx.decisions.push(extractor.decision_record(
                egraph,
                eclass,
                ctx.axiom_name,
                *ctx.slot_index,
                expr,
            ));
            *ctx.slot_index += 1;

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
    let expr = extractor.extract(egraph, eclass.id);
    if trace_conflicts_enabled() {
        trace_conflicts(format!(
            "      choice slot={} axiom={} eclass={} expr={}",
            *ctx.slot_index, ctx.axiom_name, eclass.id, expr
        ));
    }
    debug!("    extraction: {} -> {}", eclass.id, expr.pretty(80));
    ctx.decisions.push(extractor.decision_record(
        egraph,
        eclass.id,
        ctx.axiom_name,
        *ctx.slot_index,
        &expr,
    ));
    *ctx.slot_index += 1;

    // wrap everything in an ENodeOrVar so that it still counts as an egg::PatternAst
    expr.as_ref()
        .iter()
        .cloned()
        .map(egg::ENodeOrVar::ENode)
        .collect::<Vec<_>>()
        .into()
}
