use std::{cell::RefCell, collections::HashMap, rc::Rc};

use egg::{Analysis, Language};
use itertools::Itertools;
use log::{debug, info};

use crate::{
    array_axioms::{ArrayExpr, ArrayLanguage},
    cost_functions::YardbirdCostFunction,
    egg_utils::RecExprRoot,
    extractor::TermExtractor,
};

pub struct ConflictScheduler<S, CF>
where
    CF: YardbirdCostFunction,
{
    inner: S,
    /// TODO: use RecExpr instead of String
    /// Keep track of rule instantiations that caused conflicts. We use an
    /// `Rc<RefCell<...>>` here because the scheduler isn't public on `egg::Runner`. So
    /// in order to be able to get data out of the scheduler after a saturation run, we
    /// need to use interior mutability.
    instantiations: Rc<RefCell<Vec<ArrayExpr>>>,
    instantiations_w_constants: Rc<RefCell<Vec<ArrayExpr>>>,
    pub cost_fn: CF,
    extractor: TermExtractor<CF>,
}

impl<S, CF> ConflictScheduler<S, CF>
where
    CF: YardbirdCostFunction,
{
    pub fn new(scheduler: S, cost_fn: CF, extractor: TermExtractor<CF>) -> Self {
        Self {
            inner: scheduler,
            instantiations: Rc::new(RefCell::new(vec![])),
            instantiations_w_constants: Rc::new(RefCell::new(vec![])),
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
}

impl<S, N, CF> egg::RewriteScheduler<ArrayLanguage, N> for ConflictScheduler<S, CF>
where
    S: egg::RewriteScheduler<ArrayLanguage, N>,
    CF: YardbirdCostFunction,
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
        self.inner.search_rewrite(iteration, egraph, rewrite)
    }

    fn apply_rewrite(
        &mut self,
        _iteration: usize,
        egraph: &mut egg::EGraph<ArrayLanguage, N>,
        rewrite: &egg::Rewrite<ArrayLanguage, N>,
        matches: Vec<egg::SearchMatches<ArrayLanguage>>,
    ) -> usize {
        debug!("======>");
        debug!("applying {}", rewrite.name);

        for m in &matches {
            if let Some(searcher_ast) = &m.ast {
                info!("Number of subs: {}", m.substs.len());
                for subst in &m.substs {
                    info!("Current Sub: {:?}", subst);

                    if let Some(applier_ast) = rewrite.applier.get_pattern_ast() {
                        // construct a new term by instantiating variables in the pattern ast with terms
                        // from the substitution.
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
                            let cost = self.cost_fn.cost_rec(&new_rhs);
                            info!(
                                "FOUND VIOLATION (cost {}): \n{}",
                                cost,
                                instantiation.pretty(80)
                            );

                            if cost >= 100 {
                                debug!("rejecting because of cost");
                                self.instantiations_w_constants
                                    .borrow_mut()
                                    .push(instantiation);
                            } else {
                                self.instantiations.borrow_mut().push(instantiation);
                            }
                        }
                    }
                }
            }
        }
        // let n = self
        //     .inner
        //     .apply_rewrite(iteration, egraph, rewrite, matches);
        debug!("<======");
        // we don't actually want to apply the rewrite, because it would be a violation
        0
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
    subst: &egg::Subst,
    extractor: &TermExtractor<CF>,
    memo: &mut HashMap<egg::Var, egg::PatternAst<ArrayLanguage>>,
) -> egg::PatternAst<ArrayLanguage>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction,
{
    match pattern.as_ref() {
        [node] => {
            match node {
                x @ egg::ENodeOrVar::ENode(_) => vec![x.clone()].into(),
                egg::ENodeOrVar::Var(var) => {
                    // let eclass = &egraph[*subst.get(*var).unwrap()];
                    // find_best_variable_substitution(eclass, extractor)
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
            use egg::ENodeOrVar as E;
            pattern
                .root()
                .clone()
                .join_recexprs(|id| match pattern[id].clone() {
                    x @ E::ENode(ArrayLanguage::Write([array, index, val])) => {
                        match (&pattern[array], &pattern[index], &pattern[val]) {
                            (E::Var(array), E::Var(index), E::Var(val)) => {
                                let array_ecls = &egraph[*subst.get(*array).unwrap()];
                                let index_ecls = &egraph[*subst.get(*index).unwrap()];
                                let val_ecls = &egraph[*subst.get(*val).unwrap()];

                                // TODO: this only works for stores into a variable
                                if let Some((array_node, index_node)) = array_ecls
                                    .nodes
                                    .iter()
                                    .flat_map(|node| {
                                        extractor
                                            .reads_and_writes
                                            .write_array(node)
                                            // only keep items contained in index eclass
                                            .flat_map(|idx| idx.parse())
                                            .filter(|idx| {
                                                egraph_contains_at(egraph, idx, index_ecls.id)
                                            })
                                            .map(|idx| (node.clone(), idx))
                                    })
                                    .next()
                                {
                                    if let Some(val_node) = extractor
                                        .reads_and_writes
                                        .write_array_index(array_node.clone(), index_node.clone())
                                        .flat_map(|v| v.parse())
                                        .find(|v| egraph_contains_at(egraph, v, val_ecls.id))
                                    {
                                        let array_expr = egg::RecExpr::from(vec![array_node]);
                                        memo.insert(*array, patternify(&array_expr));
                                        memo.insert(*index, patternify(&index_node));
                                        memo.insert(*val, patternify(&val_node));
                                        patternify(&ArrayLanguage::write(
                                            array_expr, index_node, val_node,
                                        ))
                                    } else {
                                        todo!()
                                    }
                                } else {
                                    // TODO: temporary fallback until we can handle array expressions that aren't variables
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
                            }
                            _ => todo!(),
                        }
                    }
                    E::ENode(ArrayLanguage::Read([array, index])) => {
                        match (&pattern[array], &pattern[index]) {
                            (E::Var(array), E::Var(index)) => {
                                let array_ecls = &egraph[*subst.get(*array).unwrap()];
                                let index_ecls = &egraph[*subst.get(*index).unwrap()];

                                if let Some((array_node, index_node)) = array_ecls
                                    .nodes
                                    .iter()
                                    .flat_map(|node| {
                                        extractor
                                            .reads_and_writes
                                            .read_array(node)
                                            .flat_map(|idx| idx.parse())
                                            .filter(|idx| {
                                                egraph_contains_at(egraph, idx, index_ecls.id)
                                            })
                                            .map(|idx| (node.clone(), idx))
                                    })
                                    .next()
                                {
                                    let array_expr = egg::RecExpr::from(vec![array_node]);
                                    memo.insert(*array, patternify(&array_expr));
                                    memo.insert(*index, patternify(&index_node));
                                    patternify(&ArrayLanguage::read(array_expr, index_node))
                                } else {
                                    todo!()
                                }
                            }
                            _ => todo!(),
                        }
                    }
                    x @ egg::ENodeOrVar::ENode(_) => {
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
                    egg::ENodeOrVar::Var(var) => {
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
fn egraph_contains_at<N>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    rec_expr: &egg::RecExpr<ArrayLanguage>,
    eclass_id: egg::Id,
) -> bool
where
    N: egg::Analysis<ArrayLanguage>,
{
    let expr_id = rec_expr.as_ref().len() - 1;
    egraph_contains_at_helper(egraph, rec_expr, eclass_id, expr_id.into())
}

fn egraph_contains_at_helper<N>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    rec_expr: &egg::RecExpr<ArrayLanguage>,
    eclass_id: egg::Id,
    expr_id: egg::Id,
) -> bool
where
    N: egg::Analysis<ArrayLanguage>,
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
                        egraph_contains_at_helper(egraph, rec_expr, *eclass_id, *expr_id)
                    })
            }
        })
}

fn patternify(expr: &egg::RecExpr<ArrayLanguage>) -> egg::PatternAst<ArrayLanguage> {
    expr.as_ref()
        .iter()
        .cloned()
        .map(egg::ENodeOrVar::ENode)
        .collect::<Vec<_>>()
        .into()
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
    extractor: &TermExtractor<CF>,
) -> egg::PatternAst<ArrayLanguage>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction,
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
