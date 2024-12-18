use std::rc::Rc;

use egg::*;

use crate::{
    conflict_scheduler::ConflictScheduler,
    cost::BestVariableSubstitution,
    egg_utils::{DefaultCostFunction, Saturate},
};

define_language! {
    pub enum ArrayLanguage {
        Num(i64),
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
        Symbol(Symbol),
    }
}

impl<N> Saturate for EGraph<ArrayLanguage, N>
where
    N: Analysis<ArrayLanguage> + Default + 'static,
{
    type Ret = (Vec<String>, Vec<String>);
    fn saturate(&mut self) -> (Vec<String>, Vec<String>) {
        let egraph = std::mem::take(self);
        let scheduler = ConflictScheduler::new(BackoffScheduler::default());
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

impl DefaultCostFunction for ArrayLanguage {
    type Cost = u32;
    type CF = BestVariableSubstitution;

    fn cost_function() -> Self::CF {
        BestVariableSubstitution
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

fn not_equal<N>(
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

    #[test]
    fn test_conditional_axioms0_with_scheduluer() {
        init();
        let expr: RecExpr<ArrayLanguage> =
            "(Read-Int-Int (Write-Int-Int A 0 0) 1)".parse().unwrap();

        let scheduler = ConflictScheduler::new(BackoffScheduler::default());
        let instantiations = scheduler.instantiations();
        let const_instantiations = scheduler.instantiations_w_constants();
        let _runner = Runner::default()
            .with_expr(&expr)
            .with_scheduler(scheduler)
            .run(&array_axioms::<()>());

        assert!(instantiations.borrow().len() == 0 && const_instantiations.borrow().len() == 1);
    }

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
