use std::rc::Rc;

use egg::*;
use log::debug;
use smt2parser::concrete::{Constant, QualIdentifier, Term};

use crate::{
    cost_functions::YardbirdCostFunction,
    theories::array::{
        array_conflict_scheduler::ArrayConflictScheduler, array_term_extractor::ArrayTermExtractor,
    },
};

define_language! {
    pub enum ArrayLanguage {
        Num(u64),
        // Parameterized array operations that include sort information as Symbol children
        // Format: "ConstArr" [index_sort_symbol, value_sort_symbol, value]
        "ConstArr" = ConstArrTyped([Id; 3]),
        // Format: "Write" [index_sort_symbol, value_sort_symbol, array, index, value]
        "Write" = WriteTyped([Id; 5]),
        // Format: "Read" [index_sort_symbol, value_sort_symbol, array, index]
        "Read" = ReadTyped([Id; 4]),
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

    pub fn sort_to_name(sort: &smt2parser::concrete::Sort) -> String {
        use smt2parser::concrete::{Identifier, Sort};
        match sort {
            Sort::Simple { identifier } => match identifier {
                Identifier::Simple { symbol } => symbol.0.clone(),
                Identifier::Indexed { symbol, indices } => {
                    // For indexed identifiers like (_ BitVec 32), format as "BitVec32"
                    let indices_str = indices
                        .iter()
                        .map(|idx| match idx {
                            smt2parser::visitors::Index::Numeral(n) => n.to_string(),
                            smt2parser::visitors::Index::Symbol(s) => s.0.clone(),
                        })
                        .collect::<Vec<_>>()
                        .join("_");
                    format!("{}{}", symbol.0, indices_str)
                }
            },
            Sort::Parameterized {
                identifier: _,
                parameters,
            } => parameters
                .iter()
                .map(Self::sort_to_name)
                .collect::<Vec<_>>()
                .join("_"),
        }
    }

    /// Format a typed array operation name (e.g., "Read_BitVec5_BitVec32" or "Read_Int_Array_Int_Int")
    pub fn format_array_op_name(op: &str, index_sort: &str, value_sort: &str) -> String {
        format!("{}_{}_{}", op, index_sort, value_sort)
    }

    pub fn extract_array_sorts(
        array_sort: &smt2parser::concrete::Sort,
    ) -> Option<(smt2parser::concrete::Sort, smt2parser::concrete::Sort)> {
        use smt2parser::concrete::{Identifier, Sort};
        match array_sort {
            Sort::Parameterized {
                identifier,
                parameters,
            } => {
                let is_array = match identifier {
                    Identifier::Simple { symbol } => symbol.0 == "Array",
                    Identifier::Indexed { symbol, .. } => symbol.0 == "Array",
                };
                if is_array && parameters.len() == 2 {
                    Some((parameters[0].clone(), parameters[1].clone()))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn read_typed(
        index_sort: &str,
        value_sort: &str,
        array: ArrayExpr,
        index: ArrayExpr,
    ) -> ArrayExpr {
        let mut expr = egg::RecExpr::default();
        let is = expr.add(ArrayLanguage::Symbol(index_sort.into()));
        let vs = expr.add(ArrayLanguage::Symbol(value_sort.into()));
        let a = expr.add(ArrayLanguage::Symbol("a".into()));
        let i = expr.add(ArrayLanguage::Symbol("i".into()));
        let read = expr.add(ArrayLanguage::ReadTyped([is, vs, a, i]));

        expr[read].join_recexprs(|id| {
            if id == a {
                array.clone()
            } else if id == i {
                index.clone()
            } else if id == is || id == vs {
                // Keep sort symbols as-is (they're not placeholders)
                RecExpr::from(vec![expr[id].clone()])
            } else {
                unreachable!()
            }
        })
    }

    pub fn write_typed(
        index_sort: &str,
        value_sort: &str,
        array: ArrayExpr,
        index: ArrayExpr,
        value: ArrayExpr,
    ) -> ArrayExpr {
        let mut expr = egg::RecExpr::default();
        let is = expr.add(ArrayLanguage::Symbol(index_sort.into()));
        let vs = expr.add(ArrayLanguage::Symbol(value_sort.into()));
        let a = expr.add(ArrayLanguage::Symbol("a".into()));
        let i = expr.add(ArrayLanguage::Symbol("i".into()));
        let v = expr.add(ArrayLanguage::Symbol("v".into()));
        let write = expr.add(ArrayLanguage::WriteTyped([is, vs, a, i, v]));

        expr[write].join_recexprs(|id| {
            if id == a {
                array.clone()
            } else if id == i {
                index.clone()
            } else if id == v {
                value.clone()
            } else if id == is || id == vs {
                // Keep sort symbols as-is (they're not placeholders)
                RecExpr::from(vec![expr[id].clone()])
            } else {
                unreachable!()
            }
        })
    }

    pub fn const_arr_typed(index_sort: &str, value_sort: &str, value: ArrayExpr) -> ArrayExpr {
        let mut expr = egg::RecExpr::default();
        let is = expr.add(ArrayLanguage::Symbol(index_sort.into()));
        let vs = expr.add(ArrayLanguage::Symbol(value_sort.into()));
        let v = expr.add(ArrayLanguage::Symbol("v".into()));
        let const_arr = expr.add(ArrayLanguage::ConstArrTyped([is, vs, v]));

        expr[const_arr].join_recexprs(|id| {
            if id == v {
                value.clone()
            } else if id == is || id == vs {
                // Keep sort symbols as-is (they're not placeholders)
                RecExpr::from(vec![expr[id].clone()])
            } else {
                unreachable!()
            }
        })
    }
}

pub fn saturate_with_array_types<CF, N>(
    egraph: &mut EGraph<ArrayLanguage, N>,
    cost_fn: CF,
    refinement_step: u32,
    array_types: &[(String, String)],
) -> (Vec<ArrayExpr>, Vec<ArrayExpr>)
where
    N: Analysis<ArrayLanguage> + Default + 'static,
    CF: YardbirdCostFunction<ArrayLanguage> + 'static,
{
    let taken_egraph = std::mem::take(egraph);
    let scheduler = ArrayConflictScheduler::new(
        BackoffScheduler::default(),
        cost_fn.clone(),
        ArrayTermExtractor::new(&taken_egraph, cost_fn, refinement_step),
    );
    let instantiations = scheduler.instantiations();
    let const_instantiations = scheduler.instantiations_w_constants();
    let axioms = array_axioms_with_types(array_types);

    #[cfg(debug_assertions)]
    {
        for class in taken_egraph.classes() {
            for node in &class.nodes {
                let node_str = format!("{:?}", node);
                if node_str.contains("Read")
                    || node_str.contains("Write")
                    || node_str.contains("Symbol(\"Int\")")
                {
                    debug!("ClassID={:?}, Node: {:?}", class.id, node);
                }
            }
        }
    }

    let runner = Runner::default()
        .with_egraph(taken_egraph)
        .with_scheduler(scheduler)
        .run(&axioms);

    drop(runner);

    let final_insts = Rc::into_inner(instantiations).unwrap().into_inner();
    let final_const_insts = Rc::into_inner(const_instantiations).unwrap().into_inner();

    #[cfg(debug_assertions)]
    {
        debug!("=== FINAL INSTANTIATIONS ===");
        debug!("Regular: {}", final_insts.len());
        for (i, inst) in final_insts.iter().enumerate() {
            debug!("  [{}]: {}", i, inst);
        }
        debug!("Const: {}", final_const_insts.len());
        for (i, inst) in final_const_insts.iter().enumerate() {
            debug!("  [{}]: {}", i, inst);
        }
        debug!("============================\n");
    }

    (final_insts, final_const_insts)
}

/// Generate array axioms for a specific type pair (index_sort, value_sort).
/// This creates type-specific versions of the three core array axioms.
fn array_axioms_for_type<N>(index_sort: &str, value_sort: &str) -> Vec<Rewrite<ArrayLanguage, N>>
where
    N: Analysis<ArrayLanguage> + 'static,
{
    // Axiom 1: write-does-not-overwrite
    // (Read (Write a idx val) c) => (Read a c) when idx != c
    let axiom_name_1 = format!("write-does-not-overwrite-{}-{}", index_sort, value_sort);
    let pattern_1 = format!(
        "(Read {} {} (Write {} {} ?a ?idx ?val) ?c)",
        index_sort, value_sort, index_sort, value_sort
    );
    let replacement_1 = format!("(Read {} {} ?a ?c)", index_sort, value_sort);
    let parsed_pattern: egg::Pattern<ArrayLanguage> = pattern_1.parse().unwrap();
    let axiom_1 = Rewrite::new(
        axiom_name_1,
        ConditionalSearcher::new(parsed_pattern, not_equal("?idx", "?c")),
        replacement_1
            .parse::<egg::Pattern<ArrayLanguage>>()
            .unwrap(),
    )
    .unwrap();

    // Axiom 2: read-after-write
    // (Read (Write a idx val) idx) => val
    let axiom_name_2 = format!("read-after-write-{}-{}", index_sort, value_sort);
    let pattern_2 = format!(
        "(Read {} {} (Write {} {} ?a ?idx ?val) ?idx)",
        index_sort, value_sort, index_sort, value_sort
    );
    let pat2 = pattern_2.parse::<egg::Pattern<ArrayLanguage>>().unwrap();
    let replacement_2 = "?val";
    let axiom_2 = Rewrite::new(
        axiom_name_2,
        pat2,
        replacement_2
            .parse::<egg::Pattern<ArrayLanguage>>()
            .unwrap(),
    )
    .unwrap();

    let axiom_name_3 = format!("constant-array-{}-{}", index_sort, value_sort);
    let pattern_3 = format!(
        "(Read {} {} (ConstArr {} {} ?a) ?b)",
        index_sort, value_sort, index_sort, value_sort
    );
    let pat3 = pattern_3.parse::<egg::Pattern<ArrayLanguage>>().unwrap();
    let replacement_3 = "?a";
    let axiom_3 = Rewrite::new(
        axiom_name_3,
        pat3,
        replacement_3
            .parse::<egg::Pattern<ArrayLanguage>>()
            .unwrap(),
    )
    .unwrap();

    vec![axiom_1, axiom_2, axiom_3]
}

/// Generate array axioms for multiple discovered array types.
/// This creates axioms for each discovered type.
fn array_axioms_with_types<N>(array_types: &[(String, String)]) -> Vec<Rewrite<ArrayLanguage, N>>
where
    N: Analysis<ArrayLanguage> + 'static,
{
    let mut all_axioms = Vec::new();
    for (index_sort, value_sort) in array_types {
        all_axioms.extend(array_axioms_for_type(index_sort, value_sort));
    }
    all_axioms
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
    fn search_with_limit(&self, egraph: &EGraph<L, N>, limit: usize) -> Vec<SearchMatches<'_, L>> {
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
            } => {
                let name = qual_identifier.get_name();

                // Check for parameterized array operations (e.g., "Read_BitVec5_BitVec32" or "Read_Int_Array_Int_Int")
                // Handle these before the match statement
                if let Some(rest) = name.strip_prefix("ConstArr_") {
                    // Parse "IndexSort_ValueSort" from the suffix - supports nested like "Int_Array_Int_Int"
                    let parts: Vec<&str> = rest.split('_').collect();
                    if parts.len() >= 2 {
                        let (index_sort, value_sort) = (parts[0], parts[1..].join("_"));
                        assert!(arguments.len() == 1);
                        let index_sort_id = expr.add(ArrayLanguage::Symbol(index_sort.into()));
                        let value_sort_id = expr.add(ArrayLanguage::Symbol(value_sort.into()));
                        let arg_id = inner(arguments.pop().unwrap(), expr)?;
                        return Some(expr.add(ArrayLanguage::ConstArrTyped([
                            index_sort_id,
                            value_sort_id,
                            arg_id,
                        ])));
                    }
                } else if let Some(rest) = name.strip_prefix("Write_") {
                    let parts: Vec<&str> = rest.split('_').collect();
                    if parts.len() >= 2 {
                        let (index_sort, value_sort) = (parts[0], parts[1..].join("_"));
                        assert!(arguments.len() == 3);
                        let index_sort_id = expr.add(ArrayLanguage::Symbol(index_sort.into()));
                        let value_sort_id = expr.add(ArrayLanguage::Symbol(value_sort.into()));
                        // args popped in reverse order
                        let val = inner(arguments.pop().unwrap(), expr)?;
                        let idx = inner(arguments.pop().unwrap(), expr)?;
                        let arr = inner(arguments.pop().unwrap(), expr)?;
                        return Some(expr.add(ArrayLanguage::WriteTyped([
                            index_sort_id,
                            value_sort_id,
                            arr,
                            idx,
                            val,
                        ])));
                    }
                } else if let Some(rest) = name.strip_prefix("Read_") {
                    let parts: Vec<&str> = rest.split('_').collect();
                    if parts.len() >= 2 {
                        let (index_sort, value_sort) = (parts[0], parts[1..].join("_"));
                        assert!(arguments.len() == 2);
                        let index_sort_id = expr.add(ArrayLanguage::Symbol(index_sort.into()));
                        let value_sort_id = expr.add(ArrayLanguage::Symbol(value_sort.into()));
                        // args popped in reverse order
                        let idx = inner(arguments.pop().unwrap(), expr)?;
                        let arr = inner(arguments.pop().unwrap(), expr)?;
                        return Some(expr.add(ArrayLanguage::ReadTyped([
                            index_sort_id,
                            value_sort_id,
                            arr,
                            idx,
                        ])));
                    }
                }

                // Original hardcoded patterns for backward compatibility (Int_Int arrays)
                match name.as_str() {
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
                }
            }
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
            ArrayLanguage::ConstArrTyped([index_sort, value_sort, x]) => {
                // Extract sort names from Symbol nodes
                let index_sort_name = match &expr[*index_sort] {
                    ArrayLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let value_sort_name = match &expr[*value_sort] {
                    ArrayLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let func_name = ArrayLanguage::format_array_op_name(
                    "ConstArr",
                    index_sort_name,
                    value_sort_name,
                );
                Term::Application {
                    qual_identifier: QualIdentifier::simple(func_name),
                    arguments: vec![inner(expr, *x)],
                }
            }
            ArrayLanguage::WriteTyped([index_sort, value_sort, arr, idx, val]) => {
                let index_sort_name = match &expr[*index_sort] {
                    ArrayLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let value_sort_name = match &expr[*value_sort] {
                    ArrayLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let func_name =
                    ArrayLanguage::format_array_op_name("Write", index_sort_name, value_sort_name);
                Term::Application {
                    qual_identifier: QualIdentifier::simple(func_name),
                    arguments: vec![inner(expr, *arr), inner(expr, *idx), inner(expr, *val)],
                }
            }
            ArrayLanguage::ReadTyped([index_sort, value_sort, arr, idx]) => {
                let index_sort_name = match &expr[*index_sort] {
                    ArrayLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let value_sort_name = match &expr[*value_sort] {
                    ArrayLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let func_name =
                    ArrayLanguage::format_array_op_name("Read", index_sort_name, value_sort_name);
                Term::Application {
                    qual_identifier: QualIdentifier::simple(func_name),
                    arguments: vec![inner(expr, *arr), inner(expr, *idx)],
                }
            }
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
            "(Read Int Int (Write Int Int A 0 0) 1)".parse().unwrap();
        let runner = Runner::default()
            .with_expr(&expr)
            .run(&array_axioms_with_types::<()>(&[(
                "Int".into(),
                "Int".into(),
            )]));

        let gold: RecExpr<ArrayLanguage> = "(Read Int Int A 1)".parse().unwrap();
        assert!(runner.egraph.lookup_expr(&gold).is_some())
    }

    #[test]
    fn test_conditional_axioms1() {
        init();
        let expr: RecExpr<ArrayLanguage> =
            "(Read Int Int (Write Int Int A 0 0) 0)".parse().unwrap();
        let runner = Runner::default()
            .with_expr(&expr)
            .run(&array_axioms_with_types::<()>(&[(
                "Int".into(),
                "Int".into(),
            )]));
        let gold: RecExpr<ArrayLanguage> = "(Read Int Int A 0)".parse().unwrap();
        assert!(runner.egraph.lookup_expr(&gold).is_none())
    }

    // #[test]
    // fn test_conditional_axioms0_with_scheduluer() {
    //     init();
    //     let expr: RecExpr<ArrayLanguage> =
    //         "(Read_Int_Int (Write_Int_Int A 0 0) 1)".parse().unwrap();

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
    //         "(Read_Int_Int (Write_Int_Int A 0 0) 0)".parse().unwrap();
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
