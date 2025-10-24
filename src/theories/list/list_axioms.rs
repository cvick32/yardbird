use std::rc::Rc;

use egg::*;
use smt2parser::concrete::{Constant, QualIdentifier, Term};

use crate::{
    cost_functions::YardbirdCostFunction,
    egg_utils::Saturate,
    theories::list::{
        list_conflict_scheduler::ListConflictScheduler, list_term_extractor::ListTermExtractor,
    },
};

define_language! {
    pub enum ListLanguage {
        Num(u64),
        "nil" = Nil,
        "cons" = Cons([Id; 2]),
        "head" = Head(Id),
        "tail" = Tail(Id),
        "length" = Length(Id),
        "append" = Append([Id; 2]),
        "is-nil" = IsNil(Id),
        "nth" = Nth([Id; 2]),
        "reverse" = Reverse(Id),
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

pub type ListExpr = egg::RecExpr<ListLanguage>;
pub type ListPattern = egg::PatternAst<ListLanguage>;

impl ListLanguage {
    pub fn equals(lhs: &ListExpr, rhs: &ListExpr) -> ListExpr {
        let mut expr = egg::RecExpr::default();
        let lhs_placeholder = expr.add(ListLanguage::Symbol("lhs".into()));
        let rhs_placeholder = expr.add(ListLanguage::Symbol("rhs".into()));
        let equals = expr.add(ListLanguage::Eq([lhs_placeholder, rhs_placeholder]));

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

    pub fn not_implies(not_clause: &ListExpr, other: &ListExpr) -> ListExpr {
        let mut not_expr = egg::RecExpr::default();
        let n = not_expr.add(ListLanguage::Symbol("n".into()));
        let not = not_expr.add(ListLanguage::Not(n));

        let mut expr = egg::RecExpr::default();
        let x = expr.add(ListLanguage::Symbol("x".into()));
        let o = expr.add(ListLanguage::Symbol("o".into()));
        let implies = expr.add(ListLanguage::Implies([x, o]));

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

    pub fn cons(head: ListExpr, tail: ListExpr) -> ListExpr {
        let mut expr = egg::RecExpr::default();
        let h = expr.add(ListLanguage::Symbol("h".into()));
        let t = expr.add(ListLanguage::Symbol("t".into()));
        let cons = expr.add(ListLanguage::Cons([h, t]));

        expr[cons].join_recexprs(|id| {
            if id == h {
                head.clone()
            } else if id == t {
                tail.clone()
            } else {
                panic!()
            }
        })
    }

    pub fn head(list: ListExpr) -> ListExpr {
        let mut expr = egg::RecExpr::default();
        let l = expr.add(ListLanguage::Symbol("l".into()));
        let head = expr.add(ListLanguage::Head(l));

        expr[head].join_recexprs(|id| if id == l { list.clone() } else { panic!() })
    }

    pub fn tail(list: ListExpr) -> ListExpr {
        let mut expr = egg::RecExpr::default();
        let l = expr.add(ListLanguage::Symbol("l".into()));
        let tail = expr.add(ListLanguage::Tail(l));

        expr[tail].join_recexprs(|id| if id == l { list.clone() } else { panic!() })
    }
}

impl<CF, N> Saturate<CF, ListLanguage> for EGraph<ListLanguage, N>
where
    N: Analysis<ListLanguage> + Default + 'static,
    CF: YardbirdCostFunction<ListLanguage> + 'static,
{
    type Ret = (Vec<ListExpr>, Vec<ListExpr>);

    fn saturate(&mut self, cost_fn: CF, refinement_step: u32) -> Self::Ret {
        let egraph = std::mem::take(self);
        let scheduler = ListConflictScheduler::new(
            BackoffScheduler::default(),
            cost_fn.clone(),
            ListTermExtractor::new(&egraph, cost_fn, refinement_step),
        );
        let instantiations = scheduler.instantiations();
        let const_instantiations = scheduler.instantiations_w_constants();
        let mut runner = Runner::default()
            .with_egraph(egraph)
            .with_scheduler(scheduler)
            .run(&list_axioms());

        *self = std::mem::take(&mut runner.egraph);
        drop(runner);
        (
            Rc::into_inner(instantiations).unwrap().into_inner(),
            Rc::into_inner(const_instantiations).unwrap().into_inner(),
        )
    }
}

fn list_axioms<N>() -> Vec<Rewrite<ListLanguage, N>>
where
    N: Analysis<ListLanguage> + 'static,
{
    vec![
        // Basic list axioms
        rewrite!("head-cons"; "(head (cons ?x ?xs))" => "?x"),
        rewrite!("tail-cons"; "(tail (cons ?x ?xs))" => "?xs"),
        rewrite!("is-nil-nil";
            {
                ConditionalSearcher::new(
                    "(is-nil ?x)"
                        .parse::<egg::Pattern<ListLanguage>>()
                        .unwrap(),
                    is_nil("?x"),
                )
            }
            => "true"
        ),
        rewrite!("is-nil-cons"; "(is-nil (cons ?x ?xs))" => "false"),
        // Length axioms
        rewrite!("length-nil";
            {
                ConditionalSearcher::new(
                    "(length ?x)"
                        .parse::<egg::Pattern<ListLanguage>>()
                        .unwrap(),
                    is_nil("?x"),
                )
            }
            => "0"
        ),
        rewrite!("length-cons"; "(length (cons ?x ?xs))" => "(+ 1 (length ?xs))"),
        // Append axioms
        rewrite!("append-nil"; "(append nil ?xs)" => "?xs"),
        rewrite!("append-cons"; "(append (cons ?x ?xs) ?ys)" => "(cons ?x (append ?xs ?ys))"),
        // Nth axioms
        rewrite!("nth-cons-zero"; "(nth (cons ?x ?xs) 0)" => "?x"),
        rewrite!("nth-cons-succ"; "(nth (cons ?x ?xs) (+ 1 ?n))" => "(nth ?xs ?n)"),
        // Reverse axioms
        rewrite!("reverse-nil";
            {
                ConditionalSearcher::new(
                    "(reverse ?x)"
                        .parse::<egg::Pattern<ListLanguage>>()
                        .unwrap(),
                    is_nil("?x"),
                )
            }
            => "nil"
        ),
        rewrite!("reverse-cons"; "(reverse (cons ?x ?xs))" => "(append (reverse ?xs) (cons ?x nil))"),
        rewrite!("reverse-reverse"; "(reverse (reverse ?x))" => "?x"),
        // Composition axioms
        rewrite!("head-append-non-nil";
            {
                ConditionalSearcher::new(
                    "(head (append ?xs ?ys))"
                        .parse::<egg::Pattern<ListLanguage>>()
                        .unwrap(),
                    not_nil("?xs"),
                )
            }
            => "(head ?xs)"
        ),
        // Length composition
        rewrite!("length-append"; "(length (append ?xs ?ys))" => "(+ (length ?xs) (length ?ys))"),
        rewrite!("length-reverse"; "(length (reverse ?xs))" => "(length ?xs)"),
    ]
}

fn not_nil<N>(var: &'static str) -> impl Fn(&EGraph<ListLanguage, N>, Id, &Subst) -> bool
where
    N: Analysis<ListLanguage>,
{
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        // Check if the variable maps to any existing nil representation
        // For now, we'll use string comparison as a simple heuristic
        let var_id = subst[var];

        // Try to find if there's a nil in the egraph
        for class in egraph.classes() {
            for node in &class.nodes {
                if matches!(node, ListLanguage::Nil) {
                    return egraph.find(var_id) != class.id;
                }
            }
        }

        // If no nil found, assume it's not nil
        true
    }
}

fn is_nil<N>(var: &'static str) -> impl Fn(&EGraph<ListLanguage, N>, Id, &Subst) -> bool
where
    N: Analysis<ListLanguage>,
{
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        let var_id = subst[var];
        let var_eclass = egraph.find(var_id);

        for class in egraph.classes() {
            for node in &class.nodes {
                if node.to_string().eq("nil") {
                    return var_eclass == class.id;
                }
            }
        }

        // If no nil found, it's not nil
        false
    }
}

/// An `egg::Searcher` that only returns search results that pass a provided condition
struct ConditionalSearcher<S, C> {
    searcher: S,
    condition: C,
}

impl<S, C> ConditionalSearcher<S, C> {
    fn new(searcher: S, condition: C) -> Self {
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
    fn search_with_limit(&self, egraph: &EGraph<L, N>, limit: usize) -> Vec<SearchMatches<'_, L>> {
        self.searcher
            .search_with_limit(egraph, limit)
            .into_iter()
            .filter_map(|matches| {
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
    ) -> Option<SearchMatches<'_, L>> {
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

pub fn translate_term(term: Term) -> Option<egg::RecExpr<ListLanguage>> {
    fn inner(term: Term, expr: &mut egg::RecExpr<ListLanguage>) -> Option<egg::Id> {
        match term {
            Term::Constant(c) => Some(expr.add(ListLanguage::Symbol(c.to_string().into()))),
            Term::QualIdentifier(qi) => Some(expr.add(ListLanguage::Symbol(qi.to_string().into()))),
            Term::Application {
                qual_identifier,
                mut arguments,
            } => match qual_identifier.get_name().as_str() {
                "nil" => {
                    assert!(arguments.is_empty());
                    Some(expr.add(ListLanguage::Nil))
                }
                "cons" => {
                    assert!(arguments.len() == 2);
                    let tail = inner(arguments.pop().unwrap(), expr)?;
                    let head = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Cons([head, tail])))
                }
                "head" => {
                    assert!(arguments.len() == 1);
                    let list = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Head(list)))
                }
                "tail" => {
                    assert!(arguments.len() == 1);
                    let list = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Tail(list)))
                }
                "length" => {
                    assert!(arguments.len() == 1);
                    let list = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Length(list)))
                }
                "append" => {
                    assert!(arguments.len() == 2);
                    let second = inner(arguments.pop().unwrap(), expr)?;
                    let first = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Append([first, second])))
                }
                "is-nil" => {
                    assert!(arguments.len() == 1);
                    let list = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::IsNil(list)))
                }
                "nth" => {
                    assert!(arguments.len() == 2);
                    let index = inner(arguments.pop().unwrap(), expr)?;
                    let list = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Nth([list, index])))
                }
                "reverse" => {
                    assert!(arguments.len() == 1);
                    let list = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Reverse(list)))
                }
                "and" => {
                    let arg_ids = arguments
                        .into_iter()
                        .map(|arg| inner(arg, expr))
                        .collect::<Option<_>>()?;
                    Some(expr.add(ListLanguage::And(arg_ids)))
                }
                "not" => {
                    assert!(arguments.len() == 1);
                    let arg_id = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Not(arg_id)))
                }
                "or" => {
                    let arg_ids = arguments
                        .into_iter()
                        .map(|arg| inner(arg, expr))
                        .collect::<Option<_>>()?;
                    Some(expr.add(ListLanguage::Or(arg_ids)))
                }
                "=>" => {
                    assert!(arguments.len() == 2);
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Implies([lhs, rhs])))
                }
                "=" => {
                    assert!(arguments.len() == 2);
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Eq([lhs, rhs])))
                }
                ">=" => {
                    assert!(arguments.len() == 2);
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Geq([lhs, rhs])))
                }
                ">" => {
                    assert!(arguments.len() == 2);
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Gt([lhs, rhs])))
                }
                "<=" => {
                    assert!(arguments.len() == 2);
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Leq([lhs, rhs])))
                }
                "<" => {
                    assert!(arguments.len() == 2);
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Lt([lhs, rhs])))
                }
                "mod" => {
                    assert!(arguments.len() == 2);
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Mod([lhs, rhs])))
                }
                "+" => {
                    let arg_ids = arguments
                        .into_iter()
                        .map(|arg| inner(arg, expr))
                        .collect::<Option<_>>()?;
                    Some(expr.add(ListLanguage::Plus(arg_ids)))
                }
                "-" => {
                    let arg_ids = arguments
                        .into_iter()
                        .map(|arg| inner(arg, expr))
                        .collect::<Option<_>>()?;
                    Some(expr.add(ListLanguage::Negate(arg_ids)))
                }
                "*" => {
                    let arg_ids = arguments
                        .into_iter()
                        .map(|arg| inner(arg, expr))
                        .collect::<Option<_>>()?;
                    Some(expr.add(ListLanguage::Times(arg_ids)))
                }
                "/" => {
                    assert!(arguments.len() == 2);
                    let rhs = inner(arguments.pop().unwrap(), expr)?;
                    let lhs = inner(arguments.pop().unwrap(), expr)?;
                    Some(expr.add(ListLanguage::Div([lhs, rhs])))
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

pub fn expr_to_term(expr: ListExpr) -> Term {
    fn inner(expr: &ListExpr, id: egg::Id) -> Term {
        match &expr[id] {
            ListLanguage::Num(num) => Term::Constant(Constant::Numeral((*num).into())),
            ListLanguage::Nil => Term::QualIdentifier(QualIdentifier::simple("nil")),
            ListLanguage::Cons([head, tail]) => Term::Application {
                qual_identifier: QualIdentifier::simple("cons"),
                arguments: vec![inner(expr, *head), inner(expr, *tail)],
            },
            ListLanguage::Head(list) => Term::Application {
                qual_identifier: QualIdentifier::simple("head"),
                arguments: vec![inner(expr, *list)],
            },
            ListLanguage::Tail(list) => Term::Application {
                qual_identifier: QualIdentifier::simple("tail"),
                arguments: vec![inner(expr, *list)],
            },
            ListLanguage::Length(list) => Term::Application {
                qual_identifier: QualIdentifier::simple("length"),
                arguments: vec![inner(expr, *list)],
            },
            ListLanguage::Append([first, second]) => Term::Application {
                qual_identifier: QualIdentifier::simple("append"),
                arguments: vec![inner(expr, *first), inner(expr, *second)],
            },
            ListLanguage::IsNil(list) => Term::Application {
                qual_identifier: QualIdentifier::simple("is-nil"),
                arguments: vec![inner(expr, *list)],
            },
            ListLanguage::Nth([list, index]) => Term::Application {
                qual_identifier: QualIdentifier::simple("nth"),
                arguments: vec![inner(expr, *list), inner(expr, *index)],
            },
            ListLanguage::Reverse(list) => Term::Application {
                qual_identifier: QualIdentifier::simple("reverse"),
                arguments: vec![inner(expr, *list)],
            },
            ListLanguage::And(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("and"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            ListLanguage::Not(id) => Term::Application {
                qual_identifier: QualIdentifier::simple("not"),
                arguments: vec![inner(expr, *id)],
            },
            ListLanguage::Or(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("or"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            ListLanguage::Implies([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("=>"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ListLanguage::Eq([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("="),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ListLanguage::Geq([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple(">="),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ListLanguage::Gt([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple(">"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ListLanguage::Leq([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("<="),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ListLanguage::Lt([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("<"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ListLanguage::Mod([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("mod"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ListLanguage::Plus(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("+"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            ListLanguage::Negate(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("-"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            ListLanguage::Times(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("*"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            ListLanguage::Div([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("/"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            ListLanguage::Symbol(sym) => Term::QualIdentifier(QualIdentifier::simple(sym)),
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
    fn test_head_cons() {
        init();
        let expr: RecExpr<ListLanguage> = "(head (cons x xs))".parse().unwrap();
        let runner = Runner::default().with_expr(&expr).run(&list_axioms::<()>());

        let gold: RecExpr<ListLanguage> = "x".parse().unwrap();
        assert!(runner.egraph.lookup_expr(&gold).is_some())
    }

    #[test]
    fn test_tail_cons() {
        init();
        let expr: RecExpr<ListLanguage> = "(tail (cons x xs))".parse().unwrap();
        let runner = Runner::default().with_expr(&expr).run(&list_axioms::<()>());

        let gold: RecExpr<ListLanguage> = "xs".parse().unwrap();
        assert!(runner.egraph.lookup_expr(&gold).is_some())
    }

    #[test]
    fn test_length_cons() {
        init();
        let expr: RecExpr<ListLanguage> = "(length (cons x xs))".parse().unwrap();
        let runner = Runner::default().with_expr(&expr).run(&list_axioms::<()>());

        let gold: RecExpr<ListLanguage> = "(+ 1 (length xs))".parse().unwrap();
        assert!(runner.egraph.lookup_expr(&gold).is_some())
    }

    #[test]
    fn test_append_nil() {
        init();
        let expr: RecExpr<ListLanguage> = "(append nil xs)".parse().unwrap();
        let runner = Runner::default().with_expr(&expr).run(&list_axioms::<()>());

        let gold: RecExpr<ListLanguage> = "xs".parse().unwrap();
        assert!(runner.egraph.lookup_expr(&gold).is_some())
    }
}
