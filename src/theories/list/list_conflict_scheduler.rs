use std::{cell::RefCell, collections::HashMap, rc::Rc};

use egg::{Analysis, Language};
use itertools::Itertools;
use log::{debug, info};

use crate::{
    cost_functions::YardbirdCostFunction,
    egg_utils::RecExprRoot,
    theories::list::{
        list_axioms::{ListExpr, ListLanguage},
        list_term_extractor::ListTermExtractor,
    },
};

#[allow(dead_code)]
pub struct ListConflictScheduler<S, CF>
where
    CF: YardbirdCostFunction<ListLanguage>,
{
    inner: S,
    /// TODO: use RecExpr instead of String
    /// Keep track of rule instantiations that caused conflicts. We use an
    /// `Rc<RefCell<...>>` here because the scheduler isn't public on `egg::Runner`. So
    /// in order to be able to get data out of the scheduler after a saturation run, we
    /// need to use interior mutability.
    instantiations: Rc<RefCell<Vec<ListExpr>>>,
    instantiations_w_constants: Rc<RefCell<Vec<ListExpr>>>,
    pub cost_fn: CF,
    extractor: ListTermExtractor<CF>,
}

impl<S, CF> ListConflictScheduler<S, CF>
where
    CF: YardbirdCostFunction<ListLanguage>,
{
    pub fn new(scheduler: S, cost_fn: CF, extractor: ListTermExtractor<CF>) -> Self {
        Self {
            inner: scheduler,
            instantiations: Rc::new(RefCell::new(vec![])),
            instantiations_w_constants: Rc::new(RefCell::new(vec![])),
            cost_fn,
            extractor,
        }
    }

    pub fn instantiations(&self) -> Rc<RefCell<Vec<ListExpr>>> {
        Rc::clone(&self.instantiations)
    }

    pub fn instantiations_w_constants(&self) -> Rc<RefCell<Vec<ListExpr>>> {
        Rc::clone(&self.instantiations_w_constants)
    }
}

impl<S, N, CF> egg::RewriteScheduler<ListLanguage, N> for ListConflictScheduler<S, CF>
where
    S: egg::RewriteScheduler<ListLanguage, N>,
    CF: YardbirdCostFunction<ListLanguage>,
    N: egg::Analysis<ListLanguage>,
{
    fn can_stop(&mut self, iteration: usize) -> bool {
        self.inner.can_stop(iteration)
    }

    fn search_rewrite<'a>(
        &mut self,
        iteration: usize,
        egraph: &egg::EGraph<ListLanguage, N>,
        rewrite: &'a egg::Rewrite<ListLanguage, N>,
    ) -> Vec<egg::SearchMatches<'a, ListLanguage>> {
        self.inner.search_rewrite(iteration, egraph, rewrite)
    }

    fn apply_rewrite(
        &mut self,
        _iteration: usize,
        egraph: &mut egg::EGraph<ListLanguage, N>,
        rewrite: &egg::Rewrite<ListLanguage, N>,
        matches: Vec<egg::SearchMatches<ListLanguage>>,
    ) -> usize {
        info!("======>");
        info!("applying rewrite '{}'", rewrite.name);
        info!("{} matches found", matches.len());

        for m in matches.iter() {
            if let Some(searcher_ast) = &m.ast {
                info!("Number of subs: {}", m.substs.len());
                for subst in m.substs.iter() {
                    info!("Current sub: {:?}", subst);

                    if let Some(applier_ast) = rewrite.applier.get_pattern_ast() {
                        // For lists, we create simple equalities for axiom violations
                        let mut memo = HashMap::default();
                        let new_lhs: egg::RecExpr<_> = unpatternify(reify_pattern_ast(
                            searcher_ast.as_ref(),
                            egraph,
                            subst,
                            &self.extractor,
                            &mut memo,
                        ));

                        let new_rhs: egg::RecExpr<_> = unpatternify(reify_pattern_ast(
                            applier_ast,
                            egraph,
                            subst,
                            &self.extractor,
                            &mut memo,
                        ));

                        let rhs_eclass = egraph.lookup_expr(&new_rhs);
                        info!("LHS: {}", new_lhs.pretty(40));
                        info!("RHS: {}", new_rhs.pretty(40));
                        info!("Match eclass: {:?}, RHS eclass: {:?}", m.eclass, rhs_eclass);

                        // If this would create a new equality, it's a conflict
                        if Some(m.eclass) != rhs_eclass {
                            let instantiation: ListExpr = ListLanguage::equals(&new_lhs, &new_rhs);
                            let cost = self.cost_fn.cost_rec(&new_rhs);

                            info!(
                                "FOUND VIOLATION (cost {}): \n{}",
                                cost,
                                instantiation.pretty(80)
                            );

                            if cost >= 100 {
                                info!("Adding to constants (high cost)");
                                self.instantiations_w_constants
                                    .borrow_mut()
                                    .push(instantiation);
                            } else {
                                info!("Adding to regular instantiations (low cost)");
                                self.instantiations.borrow_mut().push(instantiation);
                            }
                        } else {
                            info!("No conflict - eclasses match");
                        }
                    } else {
                        info!("No applier AST found");
                    }
                }
            }
        }
        info!("<======");
        // Don't actually apply the rewrite, as it would be a violation
        0
    }
}

fn reify_pattern_ast<N, CF>(
    pattern: &egg::PatternAst<ListLanguage>,
    egraph: &egg::EGraph<ListLanguage, N>,
    subst: &egg::Subst,
    extractor: &ListTermExtractor<CF>,
    memo: &mut HashMap<egg::Var, egg::PatternAst<ListLanguage>>,
) -> egg::PatternAst<ListLanguage>
where
    N: egg::Analysis<ListLanguage>,
    CF: YardbirdCostFunction<ListLanguage>,
{
    match pattern.as_ref() {
        [node] => {
            match node {
                x @ egg::ENodeOrVar::ENode(_) => vec![x.clone()].into(),
                egg::ENodeOrVar::Var(var) => {
                    // Check if we've already computed this variable
                    if let Some(expr) = memo.get(var) {
                        expr.clone()
                    } else {
                        let eclass = &egraph[*subst.get(*var).unwrap()];
                        let expr = find_best_variable_substitution(egraph, eclass, extractor);
                        memo.insert(*var, expr.clone());
                        expr
                    }
                }
            }
        }
        _ => {
            // For multi-node patterns, recursively process each child
            use egg::ENodeOrVar as E;
            pattern
                .rooted()
                .clone()
                .join_recexprs(|id| match pattern[id].clone() {
                    x @ E::ENode(_) => {
                        if x.is_leaf() {
                            vec![x].into()
                        } else {
                            reify_pattern_ast(
                                &x.build_recexpr(|id| pattern[id].clone()),
                                egraph,
                                subst,
                                extractor,
                                memo,
                            )
                        }
                    }
                    E::Var(var) => {
                        if let Some(expr) = memo.get(&var) {
                            expr.clone()
                        } else {
                            let eclass = &egraph[*subst.get(var).unwrap()];
                            let expr = find_best_variable_substitution(egraph, eclass, extractor);
                            memo.insert(var, expr.clone());
                            expr
                        }
                    }
                })
        }
    }
}

/// Check if the `egraph` contains a `rec_expr` that is rooted at
/// eclass `eclass_id`.
fn _egraph_contains_at<N>(
    egraph: &egg::EGraph<ListLanguage, N>,
    rec_expr: &egg::RecExpr<ListLanguage>,
    eclass_id: egg::Id,
) -> bool
where
    N: egg::Analysis<ListLanguage>,
{
    let expr_id = rec_expr.as_ref().len() - 1;
    _egraph_contains_at_helper(egraph, rec_expr, eclass_id, expr_id.into())
}

fn _egraph_contains_at_helper<N>(
    egraph: &egg::EGraph<ListLanguage, N>,
    rec_expr: &egg::RecExpr<ListLanguage>,
    eclass_id: egg::Id,
    expr_id: egg::Id,
) -> bool
where
    N: egg::Analysis<ListLanguage>,
{
    egraph[eclass_id]
        .nodes
        .iter()
        .filter(|node| node.matches(&rec_expr[expr_id]))
        .all(|node| {
            if node.is_leaf() {
                node == &rec_expr[expr_id]
            } else {
                node.children()
                    .iter()
                    .zip_eq(rec_expr[expr_id].children())
                    .all(|(eclass_id, expr_id)| {
                        _egraph_contains_at_helper(egraph, rec_expr, *eclass_id, *expr_id)
                    })
            }
        })
}

fn _patternify(expr: &egg::RecExpr<ListLanguage>) -> egg::PatternAst<ListLanguage> {
    expr.as_ref()
        .iter()
        .cloned()
        .map(egg::ENodeOrVar::ENode)
        .collect::<Vec<_>>()
        .into()
}

fn unpatternify(pattern: egg::PatternAst<ListLanguage>) -> egg::RecExpr<ListLanguage> {
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
    egraph: &egg::EGraph<ListLanguage, N>,
    eclass: &egg::EClass<ListLanguage, <N as Analysis<ListLanguage>>::Data>,
    extractor: &ListTermExtractor<CF>,
) -> egg::PatternAst<ListLanguage>
where
    N: egg::Analysis<ListLanguage>,
    CF: YardbirdCostFunction<ListLanguage>,
{
    let expr = extractor.extract(egraph, eclass.id);
    debug!("    extraction: {} -> {}", eclass.id, expr.pretty(80));

    // wrap everything in an ENodeOrVar so that it still counts as an egg::PatternAst
    expr.as_ref()
        .iter()
        .cloned()
        .map(egg::ENodeOrVar::ENode)
        .collect::<Vec<_>>()
        .into()
}
