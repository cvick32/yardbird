use std::rc::Rc;

use egg::*;
use smt2parser::concrete::{Constant, QualIdentifier, Term};

use crate::{
    conflict_scheduler::ConflictScheduler, cost_functions::symbol_cost::BestSymbolSubstitution,
    egg_utils::Saturate, extractor::TermExtractor,
};

define_language! {
    pub enum ArrayLanguage {
        Num(u64),
        "ConstArr-Int-Int" = ConstArr([Id; 1]),
        "Write-Int-Int" = Write([Id; 3]),
        "Read-Int-Int" = Read([Id; 2]),
        "and" = And(Box<[Id]>),
        "not" = Not(Id),
        "or" = Or(Box<[Id]>),
        "=>" = Implies([Id; 2]),
        "=" = Eq([Id; 2]),
        ">=" = Geq([Id; 2]),
        ">" = Gt([Id; 2]),
        "<=" = Leq([Id; 2]),
        "<" = Lt([Id; 2]),
        "mod" = Mod([Id; 2]),
        "+" = Plus(Box<[Id]>),
        "-" = Negate(Box<[Id]>),
        "*" = Times(Box<[Id]>),
        "/" = Div([Id; 2]),
        Symbol(Symbol),
    }
}

pub type ArrayExpr = egg::RecExpr<ArrayLanguage>;
pub type ArrayPattern = egg::PatternAst<ArrayLanguage>;

impl ArrayLanguage {
    pub fn equals(lhs: &ArrayExpr, rhs: &ArrayExpr) -> ArrayExpr {
        let mut expr = egg::RecExpr::default();
        let lhs_placeholder = expr.add(ArrayLanguage::Symbol("lhs".into()));
        let rhs_placeholder = expr.add(ArrayLanguage::Symbol("rhs".into()));
        let equals = expr.add(ArrayLanguage::Eq([lhs_placeholder, rhs_placeholder]));

        expr[equals].join_recexprs(|id| {
            if id == lhs_placeholder {
                lhs.clone()
            } else if id == rhs_placeholder {
                rhs.clone()
            } else {
                unreachable!()
            }
        })
    }

    pub fn not_implies(not_clause: &ArrayExpr, other: &ArrayExpr) -> ArrayExpr {
        let mut not_expr = egg::RecExpr::default();
        let n = not_expr.add(ArrayLanguage::Symbol("n".into()));
        let not = not_expr.add(ArrayLanguage::Not(n));

        let mut expr = egg::RecExpr::default();
        let x = expr.add(ArrayLanguage::Symbol("x".into()));
        let o = expr.add(ArrayLanguage::Symbol("o".into()));
        let implies = expr.add(ArrayLanguage::Implies([x, o]));

        expr[implies].join_recexprs(|id| {
            if id == x {
                not_expr[not].join_recexprs(|id| {
                    if id == n {
                        not_clause.clone()
                    } else {
                        unreachable!()
                    }
                })
            } else if id == o {
                other.clone()
            } else {
                unreachable!()
            }
        })
    }

    pub fn read(array: ArrayExpr, index: ArrayExpr) -> ArrayExpr {
        let mut expr = egg::RecExpr::default();
        let a = expr.add(ArrayLanguage::Symbol("a".into()));
        let i = expr.add(ArrayLanguage::Symbol("i".into()));
        let write = expr.add(ArrayLanguage::Read([a, i]));

        expr[write].join_recexprs(|id| {
            if id == a {
                array.clone()
            } else if id == i {
                index.clone()
            } else {
                panic!()
            }
        })
    }

    pub fn write(array: ArrayExpr, index: ArrayExpr, value: ArrayExpr) -> ArrayExpr {
        let mut expr = egg::RecExpr::default();
        let a = expr.add(ArrayLanguage::Symbol("a".into()));
        let i = expr.add(ArrayLanguage::Symbol("i".into()));
        let v = expr.add(ArrayLanguage::Symbol("v".into()));
        let write = expr.add(ArrayLanguage::Write([a, i, v]));

        expr[write].join_recexprs(|id| {
            if id == a {
                array.clone()
            } else if id == i {
                index.clone()
            } else if id == v {
                value.clone()
            } else {
                panic!()
            }
        })
    }
}

impl<N> Saturate for EGraph<ArrayLanguage, N>
where
    N: Analysis<ArrayLanguage> + Default + 'static,
{
    type Ret = (Vec<ArrayExpr>, Vec<ArrayExpr>);
    fn saturate(&mut self, cost_fn: BestSymbolSubstitution) -> Self::Ret {
        let egraph = std::mem::take(self);
        let trans_terms = cost_fn.transition_system_terms.clone();
        let prop_terms = cost_fn.property_terms.clone();
        let reads_writes = cost_fn.reads_writes.clone();
        let scheduler = ConflictScheduler::new(
            BackoffScheduler::default(),
            cost_fn.clone(),
            TermExtractor::new(&egraph, cost_fn, &trans_terms, &prop_terms, reads_writes),
        );
        let instantiations = scheduler.instantiations();
        let const_instantiations = scheduler.instantiations_w_constants();
        let mut runner = Runner::default()
            .with_egraph(egraph)
            .with_scheduler(scheduler)
            .run(&array_axioms());

        *self = std::mem::take(&mut runner.egraph);

        drop(runner);
        (
            Rc::into_inner(instantiations).unwrap().into_inner(),
            Rc::into_inner(const_instantiations).unwrap().into_inner(),
        )
    }
}

fn array_axioms<N>() -> Vec<Rewrite<ArrayLanguage, N>>
where
    N: Analysis<ArrayLanguage> + 'static,
{
    vec![
        rewrite!("constant-array"; "(Read-Int-Int (ConstArr-Int-Int ?a) ?b)" => "?a"),
        rewrite!("read-after-write"; "(Read-Int-Int (Write-Int-Int ?a ?idx ?val) ?idx)" => "?val"),
        rewrite!(
            "write-does-not-overwrite";
            {
                ConditionalSearcher::new(
                    "(Read-Int-Int (Write-Int-Int ?a ?idx ?val) ?c)"
                        .parse::<egg::Pattern<ArrayLanguage>>()
                        .unwrap(),
                    not_equal("?idx", "?c"),
                )
            }
            => "(Read-Int-Int ?a ?c)"
        ),
    ]
}

pub fn not_equal<N>(
    index_0: &'static str,
    index_1: &'static str,
) -> impl Fn(&EGraph<ArrayLanguage, N>, Id, &Subst) -> bool
where
    N: Analysis<ArrayLanguage>,
{
    let var_0 = index_0.parse().unwrap();
    let var_1 = index_1.parse().unwrap();
    move |egraph, _, subst| egraph.find(subst[var_0]) != egraph.find(subst[var_1])
}

/// An `egg::Searcher` that only returns search results that pass a provided condition
pub struct ConditionalSearcher<S, C> {
    searcher: S,
    condition: C,
}

impl<S, C> ConditionalSearcher<S, C> {
    pub fn new(searcher: S, condition: C) -> Self {
        Self {
            searcher,
            condition,
        }
    }
}

impl<L, N, S, C> egg::Searcher<L, N> for ConditionalSearcher<S, C>
where
    L: egg::Language,
    N: egg::Analysis<L>,
    S: egg::Searcher<L, N>,
    C: Fn(&egg::EGraph<L, N>, egg::Id, &egg::Subst) -> bool,
{
    fn search_with_limit(&self, egraph: &EGraph<L, N>, limit: usize) -> Vec<SearchMatches<L>> {
        self.searcher
            .search_with_limit(egraph, limit)
            .into_iter()
            .filter_map(|matches| {
                // only return substs that pass the provided condition
                let substs: Vec<_> = matches
                    .substs
                    .into_iter()
                    .filter(|subst| (self.condition)(egraph, matches.eclass, subst))
                    .collect();
                if substs.is_empty() {
                    None
                } else {
                    Some(SearchMatches {
                        eclass: matches.eclass,
                        substs,
                        ast: matches.ast,
                    })
                }
            })
            .collect()
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<L, N>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<L>> {
        self.searcher
            .search_eclass_with_limit(egraph, eclass, limit)
            .map(|matches| SearchMatches {
                eclass: matches.eclass,
                substs: matches
                    .substs
                    .into_iter()
                    .filter(|subst| (self.condition)(egraph, matches.eclass, subst))
                    .collect(),
                ast: matches.ast,
            })
    }

    fn vars(&self) -> Vec<Var> {
        self.searcher.vars()
    }

    fn get_pattern_ast(&self) -> Option<&PatternAst<L>> {
        self.searcher.get_pattern_ast()
    }
}

/// Expermiental transformation from Term directly to egg::RecExpr,
/// so that we can skip using strings as an intermediate representation
pub fn translate_term(term: Term) -> Option<egg::RecExpr<ArrayLanguage>> {
    fn inner(term: Term, expr: &mut egg::RecExpr<ArrayLanguage>) -> Option<egg::Id> {
        match term {
            Term::Constant(c) => Some(expr.add(ArrayLanguage::Symbol(c.to_string().into()))),
            Term::QualIdentifier(qi) => {
                Some(expr.add(ArrayLanguage::Symbol(qi.to_string().into())))
            }
            Term::Application {
                qual_identifier,
                mut arguments,
            } => match qual_identifier.get_name().as_str() {
                "ConstArr-Int-Int" => {
                    assert!(arguments.len() == 1);
                    let arg_id = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::ConstArr([arg_id])))
                }
                "Write-Int-Int" => {
                    assert!(arguments.len() == 3);
                    // args popped in reverse order
                    let val = inner(arguments.pop().unwrap(), expr)?;
                    let idx = inner(arguments.pop().unwrap(), expr)?;
                    let arr = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Write([arr, idx, val])))
                }
                "Read-Int-Int" => {
                    assert!(arguments.len() == 2);
                    // args popped in reverse order
                    let idx = inner(arguments.pop().unwrap(), expr)?;
                    let arr = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Read([arr, idx])))
                }
                "and" => {
                    let arg_ids = arguments
                        .into_iter()
                        .map(|arg| inner(arg, expr))
                        .collect::<Option<_>>()?;
                    Some(expr.add(ArrayLanguage::And(arg_ids)))
                }
                "not" => {
                    assert!(arguments.len() == 1);
                    let arg_id = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Not(arg_id)))
                }
                "or" => {
                    let arg_ids = arguments
                        .into_iter()
                        .map(|arg| inner(arg, expr))
                        .collect::<Option<_>>()?;
                    Some(expr.add(ArrayLanguage::Or(arg_ids)))
                }
                "=>" => {
                    assert!(arguments.len() == 2);
                    // args popped in reverse order
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Implies([lhs, rhs])))
                }
                "=" => {
                    assert!(arguments.len() == 2);
                    // args popped in reverse order
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Eq([lhs, rhs])))
                }
                ">=" => {
                    assert!(arguments.len() == 2);
                    // args popped in reverse order
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Geq([lhs, rhs])))
                }
                ">" => {
                    assert!(arguments.len() == 2);
                    // args popped in reverse order
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Gt([lhs, rhs])))
                }
                "<=" => {
                    assert!(arguments.len() == 2);
                    // args popped in reverse order
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Leq([lhs, rhs])))
                }
                "<" => {
                    assert!(arguments.len() == 2);
                    // args popped in reverse order
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Lt([lhs, rhs])))
                }
                "mod" => {
                    assert!(arguments.len() == 2);
                    // args popped in reverse order
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Mod([lhs, rhs])))
                }
                "+" => {
                    let arg_ids = arguments
                        .into_iter()
                        .map(|arg| inner(arg, expr))
                        .collect::<Option<_>>()?;
                    Some(expr.add(ArrayLanguage::Plus(arg_ids)))
                }
                "-" => {
                    let arg_ids = arguments
                        .into_iter()
                        .map(|arg| inner(arg, expr))
                        .collect::<Option<_>>()?;
                    Some(expr.add(ArrayLanguage::Negate(arg_ids)))
                }
                "*" => {
                    let arg_ids = arguments
                        .into_iter()
                        .map(|arg| inner(arg, expr))
                        .collect::<Option<_>>()?;
                    Some(expr.add(ArrayLanguage::Times(arg_ids)))
                }
                "/" => {
                    assert!(arguments.len() == 2);
                    // args popped in reverse order
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ArrayLanguage::Div([lhs, rhs])))
                }
                x => todo!("Unsupported operator: {x}"),
            },
            Term::Forall { .. } => None,
            x @ (Term::Let { .. }
            | Term::Exists { .. }
            | Term::Match { .. }
            | Term::Attributes { .. }) => todo!("{x}"),
        }
    }

    let mut expr = egg::RecExpr::default();
    inner(term, &mut expr)?;
    Some(expr)
}

pub fn expr_to_term(expr: ArrayExpr) -> Term {
    fn inner(expr: &ArrayExpr, id: egg::Id) -> Term {
        match &expr[id] {
            ArrayLanguage::Num(num) => Term::Constant(Constant::Numeral((*num).into())),
            ArrayLanguage::ConstArr([x]) => Term::Application {
                qual_identifier: QualIdentifier::simple("ConstArr-Int-Int"),
                arguments: vec![inner(expr, *x)],
            },
            ArrayLanguage::Write([arr, idx, val]) => Term::Application {
                qual_identifier: QualIdentifier::simple("Write-Int-Int"),
                arguments: vec![inner(expr, *arr), inner(expr, *idx), inner(expr, *val)],
            },
            ArrayLanguage::Read([arr, idx]) => Term::Application {
                qual_identifier: QualIdentifier::simple("Read-Int-Int"),
                arguments: vec![inner(expr, *arr), inner(expr, *idx)],
            },
            ArrayLanguage::And(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("and"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            ArrayLanguage::Not(id) => Term::Application {
                qual_identifier: QualIdentifier::simple("not"),
                arguments: vec![inner(expr, *id)],
            },
            ArrayLanguage::Or(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("or"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            ArrayLanguage::Implies([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("=>"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ArrayLanguage::Eq([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("="),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ArrayLanguage::Geq([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple(">="),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ArrayLanguage::Gt([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple(">"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ArrayLanguage::Leq([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("<="),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ArrayLanguage::Lt([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("<"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ArrayLanguage::Mod([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("mod"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ArrayLanguage::Plus(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("+"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            ArrayLanguage::Negate(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("-"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            ArrayLanguage::Times(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("*"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            ArrayLanguage::Div([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("/"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ArrayLanguage::Symbol(sym) => Term::QualIdentifier(QualIdentifier::simple(sym)),
        }
    }

    inner(&expr, egg::Id::from(expr.as_ref().len() - 1))
}

#[cfg(test)]
mod test {
    use super::*;

    fn init() {
        let _ = env_logger::builder()
            .is_test(true)
            .filter_level(log::LevelFilter::Debug)
            .filter_module("egg", log::LevelFilter::Off)
            .filter_module("z3", log::LevelFilter::Off)
            .try_init();
    }

    #[test]
    fn test_conditional_axioms0() {
        init();
        let expr: RecExpr<ArrayLanguage> =
            "(Read-Int-Int (Write-Int-Int A 0 0) 1)".parse().unwrap();
        let runner = Runner::default()
            .with_expr(&expr)
            .run(&array_axioms::<()>());

        let gold: RecExpr<ArrayLanguage> = "(Read-Int-Int A 1)".parse().unwrap();
        assert!(runner.egraph.lookup_expr(&gold).is_some())
    }

    #[test]
    fn test_conditional_axioms1() {
        init();
        let expr: RecExpr<ArrayLanguage> =
            "(Read-Int-Int (Write-Int-Int A 0 0) 0)".parse().unwrap();
        let runner = Runner::default()
            .with_expr(&expr)
            .run(&array_axioms::<()>());

        let gold: RecExpr<ArrayLanguage> = "(Read-Int-Int A 0)".parse().unwrap();
        assert!(runner.egraph.lookup_expr(&gold).is_none())
    }

    // #[test]
    // fn test_conditional_axioms0_with_scheduluer() {
    //     init();
    //     let expr: RecExpr<ArrayLanguage> =
    //         "(Read-Int-Int (Write-Int-Int A 0 0) 1)".parse().unwrap();

    //     let scheduler = ConflictScheduler::new(BackoffScheduler::default());
    //     let instantiations = scheduler.instantiations();
    //     let const_instantiations = scheduler.instantiations_w_constants();
    //     let _runner = Runner::default()
    //         .with_expr(&expr)
    //         .with_scheduler(scheduler)
    //         .run(&array_axioms::<()>());

    //     assert!(instantiations.borrow().len() == 0 && const_instantiations.borrow().len() == 1);
    // }

    // #[test]
    // fn test_conditional_axioms1_with_scheduler() {
    //     init();
    //     let expr: RecExpr<ArrayLanguage> =
    //         "(Read-Int-Int (Write-Int-Int A 0 0) 0)".parse().unwrap();
    //     let scheduler = ConflictScheduler::new(BackoffScheduler::default());
    //     let instantiations = scheduler.instantiations_w_constants();
    //     let const_instantiations = scheduler.instantiations_w_constants();
    //     let _runner = Runner::default()
    //         .with_expr(&expr)
    //         .with_scheduler(scheduler)
    //         .run(&array_axioms::<()>());

    //     assert!(instantiations.borrow().len() == 0 && const_instantiations.borrow().len() == 0);
    // }
}
