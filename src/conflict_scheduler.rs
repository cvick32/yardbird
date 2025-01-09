use std::{cell::RefCell, rc::Rc};

use egg::{Analysis, Language};
use log::{debug, info};

use crate::{egg_utils::RecExprRoot, extractor::TermExtractor};

pub struct ConflictScheduler<S, CF> {
    inner: S,
    /// TODO: use RecExpr instead of String
    /// Keep track of rule instantiations that caused conflicts. We use an
    /// `Rc<RefCell<...>>` here because the scheduler isn't public on `egg::Runner`. So
    /// in order to be able to get data out of the scheduler after a saturation run, we
    /// need to use interior mutability.
    instantiations: Rc<RefCell<Vec<String>>>,
    instantiations_w_constants: Rc<RefCell<Vec<String>>>,
    cost_fn: CF,
    transition_system_terms: Vec<String>,
    property_terms: Vec<String>,
}

impl<S, CF> ConflictScheduler<S, CF> {
    pub fn new(
        scheduler: S,
        cost_fn: CF,
        transition_system_terms: Vec<String>,
        property_terms: Vec<String>,
    ) -> Self {
        Self {
            inner: scheduler,
            instantiations: Rc::new(RefCell::new(vec![])),
            instantiations_w_constants: Rc::new(RefCell::new(vec![])),
            cost_fn,
            transition_system_terms,
            property_terms,
        }
    }

    pub fn instantiations(&self) -> Rc<RefCell<Vec<String>>> {
        Rc::clone(&self.instantiations)
    }

    pub fn instantiations_w_constants(&self) -> Rc<RefCell<Vec<String>>> {
        Rc::clone(&self.instantiations_w_constants)
    }
}

impl<S, L, N, CF> egg::RewriteScheduler<L, N> for ConflictScheduler<S, CF>
where
    S: egg::RewriteScheduler<L, N>,
    L: egg::Language + std::fmt::Display + egg::FromOp,
    CF: egg::CostFunction<L, Cost = u32> + Clone,
    N: egg::Analysis<L>,
{
    fn can_stop(&mut self, iteration: usize) -> bool {
        self.inner.can_stop(iteration)
    }

    fn search_rewrite<'a>(
        &mut self,
        iteration: usize,
        egraph: &egg::EGraph<L, N>,
        rewrite: &'a egg::Rewrite<L, N>,
    ) -> Vec<egg::SearchMatches<'a, L>> {
        self.inner.search_rewrite(iteration, egraph, rewrite)
    }

    fn apply_rewrite(
        &mut self,
        _iteration: usize,
        egraph: &mut egg::EGraph<L, N>,
        rewrite: &egg::Rewrite<L, N>,
        matches: Vec<egg::SearchMatches<L>>,
    ) -> usize {
        debug!("======>");
        debug!("applying {}", rewrite.name);

        let extractor = TermExtractor::new(
            egraph,
            self.cost_fn.clone(),
            &self.transition_system_terms,
            &self.property_terms,
        );

        for m in &matches {
            if let Some(cow_ast) = &m.ast {
                // TODO: do something smarter than just the first subst?
                let subst = &m.substs[0];
                debug!("cur sub: {:?}", subst);

                // transform &Cow<T> -> &T
                let ast = cow_ast.as_ref();
                println!("Current Instantiation: {}", ast.pretty(80));
                println!("Number of subs: {}", m.substs.len());
                println!("Current Sub: {:?}", subst);

                // construct a new term by instantiating variables in the pattern ast with terms
                // from the substitution.
                let new_lhs: egg::RecExpr<_> =
                    unpatternify(reify_pattern_ast(ast, egraph, subst, &extractor));

                if let Some(applier_ast) = rewrite.applier.get_pattern_ast() {
                    let new_rhs: egg::RecExpr<_> =
                        unpatternify(reify_pattern_ast(applier_ast, egraph, subst, &extractor));

                    let rhs_eclass = egraph.lookup_expr(&new_rhs);
                    // the eclass that we would have inserted from this pattern
                    // would cause a union from `rhs_eclass` to `eclass`. This means it
                    // is creating an equality that wouldn't otherwise be in the
                    // e-graph. This is a conflict, so we record the rule instantiation
                    // here.
                    if Some(m.eclass) != rhs_eclass {
                        info!("FOUND VIOLATION");
                        info!("{} => {}", new_lhs.pretty(80), new_rhs.pretty(80));

                        let instantiation = if rewrite.name.as_str() == "write-does-not-overwrite" {
                            let idx1 = subst.get("?c".parse().unwrap()).unwrap();
                            let idx2 = subst.get("?idx".parse().unwrap()).unwrap();
                            let extractor = egg::Extractor::new(egraph, self.cost_fn.clone());
                            let (_, expr1) = extractor.find_best(*idx1);
                            let (_, expr2) = extractor.find_best(*idx2);
                            format!(
                                "(=> (not (= {} {})) (= {} {}))",
                                expr1, expr2, new_lhs, new_rhs
                            )
                        } else {
                            format!("(= {} {})", new_lhs, new_rhs)
                        };

                        let cost = self.cost_fn.cost_rec(&new_rhs);
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
fn reify_pattern_ast<L, N, CF>(
    pattern: &egg::PatternAst<L>,
    egraph: &egg::EGraph<L, N>,
    subst: &egg::Subst,
    extractor: &TermExtractor<CF, L, N>,
) -> egg::PatternAst<L>
where
    L: egg::Language + std::fmt::Display + egg::FromOp,
    N: egg::Analysis<L>,
    CF: egg::CostFunction<L>,
    <CF as egg::CostFunction<L>>::Cost: Ord,
{
    if pattern.as_ref().len() == 1 {
        let node = &pattern.as_ref()[0];
        match node {
            x @ egg::ENodeOrVar::ENode(_) => vec![x.clone()].into(),
            egg::ENodeOrVar::Var(var) => {
                let eclass = &egraph[*subst.get(*var).unwrap()];
                find_best_variable_substitution(eclass, extractor)
            }
        }
    } else {
        pattern
            .root()
            .clone()
            .join_recexprs(|id| match pattern[id].clone() {
                x @ egg::ENodeOrVar::ENode(_) => {
                    if x.is_leaf() {
                        vec![x].into()
                    } else {
                        reify_pattern_ast(
                            &x.build_recexpr(|id| pattern[id].clone()),
                            egraph,
                            subst,
                            extractor,
                        )
                    }
                }
                egg::ENodeOrVar::Var(var) => {
                    let eclass = &egraph[*subst.get(var).unwrap()];
                    find_best_variable_substitution(eclass, extractor)
                }
            })
    }
}

fn unpatternify<L: egg::Language + std::fmt::Display>(
    pattern: egg::PatternAst<L>,
) -> egg::RecExpr<L> {
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

fn find_best_variable_substitution<L, N, CF>(
    eclass: &egg::EClass<L, <N as Analysis<L>>::Data>,
    extractor: &TermExtractor<CF, L, N>,
) -> egg::PatternAst<L>
where
    L: egg::Language + std::fmt::Display + egg::FromOp,
    N: egg::Analysis<L>,
    CF: egg::CostFunction<L>,
    <CF as egg::CostFunction<L>>::Cost: Ord,
{
    let expr = extractor.extract(eclass.id);
    debug!("    extraction: {} -> {}", eclass.id, expr.pretty(80));

    // wrap everything in an ENodeOrVar so that it still counts as an egg::PatternAst
    expr.as_ref()
        .iter()
        .cloned()
        .map(egg::ENodeOrVar::ENode)
        .collect::<Vec<_>>()
        .into()
}
