use std::{cell::RefCell, collections::HashMap, rc::Rc};

use egg::{Analysis, Language};
use itertools::Itertools;
use log::debug;

use crate::{
    cost_functions::YardbirdCostFunction,
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
        _egraph: &mut egg::EGraph<ListLanguage, N>,
        rewrite: &egg::Rewrite<ListLanguage, N>,
        matches: Vec<egg::SearchMatches<ListLanguage>>,
    ) -> usize {
        debug!("======>");
        debug!("applying {}", rewrite.name);

        for m in &matches {
            debug!("{:#?}", m);
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
fn _reify_pattern_ast<N, CF>(
    pattern: &egg::PatternAst<ListLanguage>,
    _egraph: &egg::EGraph<ListLanguage, N>,
    _subst: &egg::Subst,
    _extractor: &ListTermExtractor<CF>,
    _memo: &mut HashMap<egg::Var, egg::PatternAst<ListLanguage>>,
) -> egg::PatternAst<ListLanguage>
where
    N: egg::Analysis<ListLanguage>,
    CF: YardbirdCostFunction<ListLanguage>,
{
    pattern.clone()
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

fn _smtunpatternify(pattern: egg::PatternAst<ListLanguage>) -> egg::RecExpr<ListLanguage> {
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

fn _find_best_variable_substitution<N, CF>(
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
