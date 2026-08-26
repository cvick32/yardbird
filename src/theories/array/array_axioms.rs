use std::{cell::RefCell, rc::Rc, time::Instant};

use egg::*;
use rustc_hash::FxHashMap;
use smt2parser::concrete::{Constant, Identifier, QualIdentifier, Symbol as SmtSymbol, Term};

use crate::{
    cost_functions::YardbirdCostFunction,
    problem_context::ArrayCandidateCatalog,
    profiling::ArrayProfilingCollector,
    quantified_rule::{ArrayAxiomKind, QuantifiedRule},
    theories::array::{
        array_rule_instantiator::{
            ArrayArtifactCapture, ArrayRuleInstantiator, ArrayRuleInstantiatorOptions,
        },
        array_term_extractor::{ArrayTermExtractor, ArrayTermExtractorOptions},
        candidate_scope::CandidateScope,
        instantiation_candidate::InstantiationBatch,
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
        "to_real" = ToReal(Id),
        "ite" = Ite([Id; 3]),
        Symbol(Symbol),
    }
}

pub type ArrayExpr = egg::RecExpr<ArrayLanguage>;
pub type ArrayPattern = egg::PatternAst<ArrayLanguage>;

pub struct ArrayInstantiationInstrumentation {
    pub artifact_capture: ArrayArtifactCapture,
    pub profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

pub struct ArrayInstantiationOptions {
    pub candidate_catalog: ArrayCandidateCatalog,
    pub candidate_scope: CandidateScope,
    pub refinement_step: u32,
    pub selection_counts: FxHashMap<String, u32>,
    pub depth: u16,
    pub instrumentation: ArrayInstantiationInstrumentation,
}

fn egraph_node_count<N>(egraph: &EGraph<ArrayLanguage, N>) -> usize
where
    N: Analysis<ArrayLanguage>,
{
    egraph.classes().map(|class| class.nodes.len()).sum()
}

impl ArrayLanguage {
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

pub fn generate_array_instantiation_candidates<CF, N>(
    egraph: &EGraph<ArrayLanguage, N>,
    cost_fn: CF,
    array_types: &[(String, String)],
    options: ArrayInstantiationOptions,
) -> InstantiationBatch
where
    N: Analysis<ArrayLanguage> + 'static,
    CF: YardbirdCostFunction<ArrayLanguage> + 'static,
{
    let ArrayInstantiationOptions {
        candidate_catalog,
        candidate_scope,
        refinement_step,
        selection_counts,
        depth,
        instrumentation,
    } = options;
    let ArrayInstantiationInstrumentation {
        artifact_capture,
        profiling,
    } = instrumentation;
    if let Some(profiling) = &profiling {
        profiling
            .borrow_mut()
            .set_egraph_before_rule_search(egraph.number_of_classes(), egraph_node_count(egraph));
    }
    let instantiation_cost_fn = cost_fn.clone();
    let extractor_start = Instant::now();
    let extractor = ArrayTermExtractor::new(
        egraph,
        cost_fn,
        ArrayTermExtractorOptions {
            candidate_catalog,
            candidate_scope,
            refinement_step,
            selection_counts,
            depth,
            profiling: profiling.clone(),
        },
    );
    if let Some(profiling) = &profiling {
        profiling
            .borrow_mut()
            .record_timing("extractor_init", extractor_start.elapsed());
    }
    let rules = array_rules_with_types(array_types);
    let mut instantiator = ArrayRuleInstantiator::new(
        instantiation_cost_fn,
        extractor,
        ArrayRuleInstantiatorOptions {
            refinement_step,
            depth,
            artifact_capture,
            profiling: profiling.clone(),
        },
    );
    let search_start = Instant::now();
    let search_rounds = instantiator.search_rules(egraph, &rules);
    if let Some(profiling) = &profiling {
        profiling
            .borrow_mut()
            .record_timing("rule_search_total", search_start.elapsed());
        profiling.borrow_mut().set_egraph_after_rule_search(
            egraph.number_of_classes(),
            egraph_node_count(egraph),
            search_rounds,
        );
    }

    let candidates = instantiator.into_candidates();

    #[cfg(debug_assertions)]
    {
        log::debug!("=== FINAL INSTANTIATIONS ===");
        for (index, candidate) in candidates.iter().enumerate() {
            log::debug!("  [{}] {}", index, candidate.expression);
        }
        log::debug!("============================\n");
    }

    InstantiationBatch { candidates }
}

pub(crate) struct ArrayQuantifiedRule<N>
where
    N: Analysis<ArrayLanguage>,
{
    metadata: QuantifiedRule,
    searcher: Box<dyn Searcher<ArrayLanguage, N> + Send + Sync>,
    trigger: ArrayPattern,
    consequence: ArrayPattern,
    formula: ArrayPattern,
}

impl<N> ArrayQuantifiedRule<N>
where
    N: Analysis<ArrayLanguage>,
{
    fn new<S>(
        metadata: QuantifiedRule,
        searcher: S,
        consequence: Pattern<ArrayLanguage>,
        formula: Pattern<ArrayLanguage>,
    ) -> Result<Self, String>
    where
        S: Searcher<ArrayLanguage, N> + Send + Sync + 'static,
    {
        let trigger = searcher
            .get_pattern_ast()
            .cloned()
            .ok_or_else(|| format!("quantified rule {} has no trigger pattern", metadata.name()))?;
        let bound_variables = searcher.vars();
        for variable in consequence.vars().into_iter().chain(formula.vars()) {
            if !bound_variables.contains(&variable) {
                return Err(format!(
                    "quantified rule {} refers to unbound variable {variable}",
                    metadata.name()
                ));
            }
        }

        Ok(Self {
            metadata,
            searcher: Box::new(searcher),
            trigger,
            consequence: consequence.ast,
            formula: formula.ast,
        })
    }

    pub(crate) fn metadata(&self) -> &QuantifiedRule {
        &self.metadata
    }

    pub(crate) fn search_with_limit<'a>(
        &'a self,
        egraph: &EGraph<ArrayLanguage, N>,
        limit: usize,
    ) -> Vec<SearchMatches<'a, ArrayLanguage>> {
        self.searcher.search_with_limit(egraph, limit)
    }

    pub(crate) fn trigger(&self) -> &ArrayPattern {
        &self.trigger
    }

    pub(crate) fn consequence(&self) -> &ArrayPattern {
        &self.consequence
    }

    pub(crate) fn formula(&self) -> &ArrayPattern {
        &self.formula
    }
}

/// Generate array rules for a specific type pair (index_sort, value_sort).
/// This creates type-specific versions of the three core array axioms.
fn array_rules_for_type<N>(index_sort: &str, value_sort: &str) -> Vec<ArrayQuantifiedRule<N>>
where
    N: Analysis<ArrayLanguage> + 'static,
{
    // Axiom 1: write-does-not-overwrite
    // (Read (Write a idx val) c) => (Read a c) when idx != c
    let rule_1 = QuantifiedRule::array_axiom(
        ArrayAxiomKind::WriteDoesNotOverwrite,
        index_sort,
        value_sort,
    );
    let pattern_1 = format!(
        "(Read {} {} (Write {} {} ?a ?idx ?val) ?c)",
        index_sort, value_sort, index_sort, value_sort
    );
    let replacement_1 = format!("(Read {} {} ?a ?c)", index_sort, value_sort);
    let parsed_pattern: egg::Pattern<ArrayLanguage> = pattern_1.parse().unwrap();
    let formula_1 = format!("(=> (not (= ?c ?idx)) (= {pattern_1} {replacement_1}))");
    let axiom_1 = ArrayQuantifiedRule::new(
        rule_1,
        ConditionalSearcher::new(parsed_pattern, not_equal("?idx", "?c")),
        replacement_1.parse().unwrap(),
        formula_1.parse().unwrap(),
    )
    .unwrap();

    // Axiom 2: read-after-write
    // (Read (Write a idx val) idx) => val
    let rule_2 =
        QuantifiedRule::array_axiom(ArrayAxiomKind::ReadAfterWrite, index_sort, value_sort);
    let pattern_2 = format!(
        "(Read {} {} (Write {} {} ?a ?idx ?val) ?idx)",
        index_sort, value_sort, index_sort, value_sort
    );
    let pat2 = pattern_2.parse::<egg::Pattern<ArrayLanguage>>().unwrap();
    let replacement_2 = "?val";
    let formula_2 = format!("(= {pattern_2} {replacement_2})");
    let axiom_2 = ArrayQuantifiedRule::new(
        rule_2,
        pat2,
        replacement_2.parse().unwrap(),
        formula_2.parse().unwrap(),
    )
    .unwrap();

    let rule_3 = QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, index_sort, value_sort);
    let pattern_3 = format!(
        "(Read {} {} (ConstArr {} {} ?a) ?b)",
        index_sort, value_sort, index_sort, value_sort
    );
    let pat3 = pattern_3.parse::<egg::Pattern<ArrayLanguage>>().unwrap();
    let replacement_3 = "?a";
    let formula_3 = format!("(= {pattern_3} {replacement_3})");
    let axiom_3 = ArrayQuantifiedRule::new(
        rule_3,
        pat3,
        replacement_3.parse().unwrap(),
        formula_3.parse().unwrap(),
    )
    .unwrap();

    vec![axiom_1, axiom_2, axiom_3]
}

/// Generate executable quantified rules for all discovered array types.
fn array_rules_with_types<N>(array_types: &[(String, String)]) -> Vec<ArrayQuantifiedRule<N>>
where
    N: Analysis<ArrayLanguage> + 'static,
{
    let mut rules = Vec::new();
    for (index_sort, value_sort) in array_types {
        rules.extend(array_rules_for_type(index_sort, value_sort));
    }
    rules
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
            Term::Constant(c) => match c {
                Constant::Numeral(value) => match value.clone().try_into() {
                    Ok(value) => Some(expr.add(ArrayLanguage::Num(value))),
                    Err(_) => Some(expr.add(ArrayLanguage::Symbol(value.to_string().into()))),
                },
                other => Some(expr.add(ArrayLanguage::Symbol(other.to_string().into()))),
            },
            Term::QualIdentifier(qi) => {
                let symbol = match qi {
                    QualIdentifier::Simple {
                        identifier: Identifier::Simple { symbol },
                    } => symbol.0,
                    other => other.to_string(),
                };
                Some(expr.add(ArrayLanguage::Symbol(symbol.into())))
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
                    "to_real" => {
                        assert!(arguments.len() == 1);
                        let argument = inner(arguments.pop().unwrap(), expr)?;
                        Some(expr.add(ArrayLanguage::ToReal(argument)))
                    }
                    "ite" => {
                        assert!(arguments.len() == 3);
                        // args popped in reverse order
                        let else_term = inner(arguments.pop().unwrap(), expr)?;
                        let then_term = inner(arguments.pop().unwrap(), expr)?;
                        let condition = inner(arguments.pop().unwrap(), expr)?;
                        Some(expr.add(ArrayLanguage::Ite([condition, then_term, else_term])))
                    }
                    "bvcomp" => {
                        assert!(arguments.len() == 2);
                        let rhs = inner(arguments.pop().unwrap(), expr)?;
                        let lhs = inner(arguments.pop().unwrap(), expr)?;
                        let condition = expr.add(ArrayLanguage::Eq([lhs, rhs]));
                        let one = expr.add(ArrayLanguage::Symbol("#b1".into()));
                        let zero = expr.add(ArrayLanguage::Symbol("#b0".into()));
                        Some(expr.add(ArrayLanguage::Ite([condition, one, zero])))
                    }
                    _ => {
                        let opaque = Term::Application {
                            qual_identifier,
                            arguments,
                        }
                        .to_string();
                        Some(expr.add(ArrayLanguage::Symbol(opaque.into())))
                    }
                }
            }
            Term::Lambda { .. } | Term::Forall { .. } => None,
            Term::Attributes { term, .. } => inner(*term, expr),
            opaque @ (Term::Let { .. } | Term::Exists { .. } | Term::Match { .. }) => {
                Some(expr.add(ArrayLanguage::Symbol(opaque.to_string().into())))
            }
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
            ArrayLanguage::ToReal(argument) => Term::Application {
                qual_identifier: QualIdentifier::simple("to_real"),
                arguments: vec![inner(expr, *argument)],
            },
            ArrayLanguage::Ite([condition, then_term, else_term]) => Term::Application {
                qual_identifier: QualIdentifier::simple("ite"),
                arguments: vec![
                    inner(expr, *condition),
                    inner(expr, *then_term),
                    inner(expr, *else_term),
                ],
            },
            ArrayLanguage::Symbol(sym) => sym.as_str().parse().unwrap_or_else(|_| {
                SmtSymbol(sym.as_str().to_string())
                    .to_string()
                    .parse()
                    .expect("symbol preserved by the array e-graph must remain valid SMT-LIB")
            }),
        }
    }

    inner(&expr, egg::Id::from(expr.as_ref().len() - 1))
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use super::*;
    use crate::cost_functions::YardbirdCostFunction;
    use rustc_hash::FxHashMap;
    use smt2parser::vmt::ReadsAndWrites;

    #[derive(Clone)]
    struct ZeroCost;

    #[derive(Clone)]
    struct PreferB;

    #[derive(Clone)]
    struct HighCostA;

    const LEGACY_HIGH_COST_THRESHOLD: u32 = 100;

    fn prepare_violations(batch: &mut InstantiationBatch, scope: CandidateScope) {
        batch
            .prepare(
                scope,
                &HashSet::new(),
                |term| Ok(term.to_string().starts_with("(not ").to_string()),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();
    }

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

    impl egg::CostFunction<ArrayLanguage> for PreferB {
        type Cost = u32;

        fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            let own = match enode {
                ArrayLanguage::Symbol(symbol) if symbol.as_str() == "A" => 10,
                _ => 0,
            };
            enode.fold(own, |sum, child| sum.saturating_add(costs(child)))
        }
    }

    impl YardbirdCostFunction<ArrayLanguage> for PreferB {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }
    }

    impl egg::CostFunction<ArrayLanguage> for HighCostA {
        type Cost = u32;

        fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            let own = match enode {
                ArrayLanguage::Symbol(symbol) if symbol.as_str() == "A" => {
                    LEGACY_HIGH_COST_THRESHOLD + 1
                }
                _ => 0,
            };
            enode.fold(own, |sum, child| sum.saturating_add(costs(child)))
        }
    }

    impl YardbirdCostFunction<ArrayLanguage> for HighCostA {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }
    }

    fn init() {
        let _ = env_logger::builder()
            .is_test(true)
            .filter_level(log::LevelFilter::Debug)
            .filter_module("egg", log::LevelFilter::Off)
            .filter_module("z3", log::LevelFilter::Off)
            .try_init();
    }

    fn two_write_candidate_catalog() -> ArrayCandidateCatalog {
        let terms = [
            "A",
            "i",
            "v",
            "j",
            "B",
            "p",
            "w",
            "q",
            "(Write_Int_Int A i v)",
            "(Read_Int_Int (Write_Int_Int A i v) j)",
            "(Write_Int_Int B p w)",
            "(Read_Int_Int (Write_Int_Int B p w) q)",
        ]
        .into_iter()
        .map(str::to_string)
        .collect();

        ArrayCandidateCatalog {
            source_grounded: crate::problem_context::ArrayCandidatePool {
                terms,
                reads_and_writes: ReadsAndWrites::from(
                    std::collections::HashSet::new(),
                    std::collections::HashSet::from([
                        ("A".to_string(), "i".to_string(), "v".to_string()),
                        ("B".to_string(), "p".to_string(), "w".to_string()),
                    ]),
                ),
            },
            derived: crate::problem_context::ArrayCandidatePool::default(),
        }
    }

    #[test]
    fn write_does_not_overwrite_searcher_matches_distinct_indices() {
        init();
        let expr: RecExpr<ArrayLanguage> =
            "(Read Int Int (Write Int Int A 0 0) 1)".parse().unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&expr);
        egraph.rebuild();
        let rules = array_rules_with_types::<()>(&[("Int".into(), "Int".into())]);
        let rule = rules
            .iter()
            .find(|rule| {
                rule.metadata().kind()
                    == crate::quantified_rule::QuantifiedRuleKind::ArrayAxiom(
                        ArrayAxiomKind::WriteDoesNotOverwrite,
                    )
            })
            .unwrap();

        assert_eq!(rule.search_with_limit(&egraph, usize::MAX).len(), 1);
    }

    #[test]
    fn write_does_not_overwrite_searcher_rejects_equal_indices() {
        init();
        let expr: RecExpr<ArrayLanguage> =
            "(Read Int Int (Write Int Int A 0 0) 0)".parse().unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&expr);
        egraph.rebuild();
        let rules = array_rules_with_types::<()>(&[("Int".into(), "Int".into())]);
        let rule = rules
            .iter()
            .find(|rule| {
                rule.metadata().kind()
                    == crate::quantified_rule::QuantifiedRuleKind::ArrayAxiom(
                        ArrayAxiomKind::WriteDoesNotOverwrite,
                    )
            })
            .unwrap();

        assert!(rule.search_with_limit(&egraph, usize::MAX).is_empty());
    }

    #[test]
    fn translate_term_uses_same_numeric_encoding_as_parser() {
        let translated = translate_term(Term::Constant(Constant::Numeral(10u64.into()))).unwrap();
        let parsed: RecExpr<ArrayLanguage> = "10".parse().unwrap();

        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        let translated_id = egraph.add_expr(&translated);
        let parsed_id = egraph.add_expr(&parsed);
        egraph.rebuild();

        assert_eq!(egraph.find(translated_id), egraph.find(parsed_id));
    }

    #[test]
    fn translate_term_supports_ite() {
        let term = "(ite true x y)".parse().unwrap();
        let translated = translate_term(term).unwrap();
        let parsed: RecExpr<ArrayLanguage> = "(ite true x y)".parse().unwrap();

        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        let translated_id = egraph.add_expr(&translated);
        let parsed_id = egraph.add_expr(&parsed);
        egraph.rebuild();

        assert_eq!(egraph.find(translated_id), egraph.find(parsed_id));
        assert_eq!(expr_to_term(translated).to_string(), "(ite true x y)");
    }

    #[test]
    fn translate_term_lowers_bvcomp_without_adding_array_theory_semantics() {
        let term = "(bvcomp #b0011 #b0101)".parse().unwrap();
        let translated = translate_term(term).unwrap();

        assert_eq!(
            expr_to_term(translated).to_string(),
            "(ite (= #b0011 #b0101) #b1 #b0)"
        );
    }

    #[test]
    fn translate_term_strips_solver_metadata_attributes() {
        let term = "(! (<= x 1) :predicate true)".parse().unwrap();
        let translated = translate_term(term).unwrap();

        assert_eq!(expr_to_term(translated).to_string(), "(<= x 1)");
    }

    #[test]
    fn translate_term_preserves_to_real_coercions() {
        let term = "(to_real (- 1))".parse().unwrap();
        let translated = translate_term(term).unwrap();

        assert_eq!(expr_to_term(translated).to_string(), "(to_real (- 1))");
    }

    #[test]
    fn egraph_round_trip_does_not_embed_smt_symbol_quotes() {
        let term = Term::QualIdentifier(QualIdentifier::simple(".x{78}@1"));

        let translated = translate_term(term).unwrap();
        let round_tripped = expr_to_term(translated);

        assert_eq!(
            round_tripped,
            Term::QualIdentifier(QualIdentifier::simple(".x{78}@1"))
        );
    }

    #[test]
    fn unsupported_scalar_applications_round_trip_as_opaque_terms() {
        let term: Term = "(bvadd #b0001 #b0010)".parse().unwrap();

        let translated = translate_term(term.clone()).unwrap();

        assert_eq!(expr_to_term(translated), term);
    }

    #[test]
    fn typed_write_does_not_overwrite_instantiation_keeps_disequality_guard() {
        init();
        let expr: RecExpr<ArrayLanguage> =
            "(Read Int Int (Write Int Int A 0 0) 1)".parse().unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&expr);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            ArrayInstantiationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert_eq!(result.selected().count(), 0);
        prepare_violations(&mut result, CandidateScope::AllCandidates);
        assert_eq!(result.selected().count(), 1);
        let instantiation = result.selected().next().unwrap();
        assert!(instantiation.expression.to_string().starts_with("(=> "));

        let term = expr_to_term(instantiation.expression.clone()).to_string();
        assert_eq!(
            term,
            "(=> (not (= 1 0)) (= (Read_Int_Int (Write_Int_Int A 0 0) 1) (Read_Int_Int A 1)))"
        );
    }

    #[test]
    fn full_selection_keeps_a_candidate_from_each_violated_rule() {
        let write_does_not_overwrite: ArrayExpr =
            "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let read_after_write: ArrayExpr = "(Read Int Int (Write Int Int B k w) k)".parse().unwrap();
        let constant_array: ArrayExpr = "(Read Int Int (ConstArr Int Int z) p)".parse().unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&write_does_not_overwrite);
        egraph.add_expr(&read_after_write);
        egraph.add_expr(&constant_array);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            ArrayInstantiationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert_eq!(result.selected().count(), 0);
        prepare_violations(&mut result, CandidateScope::AllCandidates);
        let rule_names = result
            .selected()
            .map(|candidate| candidate.rule.name().to_string())
            .collect::<HashSet<_>>();
        assert_eq!(
            rule_names,
            HashSet::from([
                "write-does-not-overwrite-Int-Int".to_string(),
                "read-after-write-Int-Int".to_string(),
                "constant-array-Int-Int".to_string(),
            ])
        );
    }

    #[test]
    fn generation_borrows_the_egraph_for_staged_expansion() {
        let expr: RecExpr<ArrayLanguage> =
            "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&expr);
        egraph.rebuild();

        let _ = generate_array_instantiation_candidates(
            &egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            ArrayInstantiationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert!(
            egraph.lookup_expr(&expr).is_some(),
            "generation must leave the e-graph available for a later builder stage"
        );
    }

    #[test]
    fn source_only_generation_does_not_emit_model_derived_join() {
        init();
        let expr: RecExpr<ArrayLanguage> =
            "(Read Int Int (Write Int Int A i 137) j)".parse().unwrap();

        let run = |scope| {
            let mut egraph = EGraph::<ArrayLanguage, ()>::default();
            egraph.add_expr(&expr);
            egraph.rebuild();
            generate_array_instantiation_candidates(
                &egraph,
                ZeroCost,
                &[("Int".into(), "Int".into())],
                ArrayInstantiationOptions {
                    candidate_catalog: ArrayCandidateCatalog::default(),
                    candidate_scope: scope,
                    refinement_step: 0,
                    selection_counts: FxHashMap::default(),
                    depth: 0,
                    instrumentation: ArrayInstantiationInstrumentation {
                        artifact_capture: ArrayArtifactCapture::default(),
                        profiling: None,
                    },
                },
            )
        };

        let cone = run(CandidateScope::SourceGroundedOnly);
        let full = run(CandidateScope::AllCandidates);

        assert_eq!(cone.candidates.len(), 0);
        assert_eq!(full.candidates.len(), 1);
        assert_eq!(full.selected().count(), 0);
    }

    #[test]
    fn source_selection_ranks_complete_violations_across_rule_matches() {
        let first: ArrayExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: ArrayExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let expected: ArrayExpr =
            "(=> (not (= q p)) (= (Read Int Int (Write Int Int B p w) q) (Read Int Int B q)))"
                .parse()
                .unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&first);
        egraph.add_expr(&second);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            PreferB,
            &[("Int".into(), "Int".into())],
            ArrayInstantiationOptions {
                candidate_catalog: two_write_candidate_catalog(),
                candidate_scope: CandidateScope::SourceGroundedOnly,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert_eq!(result.selected().count(), 0);
        prepare_violations(&mut result, CandidateScope::SourceGroundedOnly);
        assert_eq!(
            result
                .selected()
                .map(|candidate| candidate.expression.clone())
                .collect::<Vec<_>>(),
            vec![expected]
        );
    }

    #[test]
    fn costs_over_100_compete_without_special_classification() {
        let first: ArrayExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: ArrayExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&first);
        egraph.add_expr(&second);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            HighCostA,
            &[("Int".into(), "Int".into())],
            ArrayInstantiationOptions {
                candidate_catalog: two_write_candidate_catalog(),
                candidate_scope: CandidateScope::SourceGroundedOnly,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert!(result
            .candidates
            .iter()
            .any(|candidate| candidate.cost > LEGACY_HIGH_COST_THRESHOLD));
        prepare_violations(&mut result, CandidateScope::SourceGroundedOnly);
        assert!(result
            .selected()
            .all(|candidate| candidate.cost <= LEGACY_HIGH_COST_THRESHOLD));

        result
            .candidates
            .retain(|candidate| candidate.cost > LEGACY_HIGH_COST_THRESHOLD);
        prepare_violations(&mut result, CandidateScope::SourceGroundedOnly);
        assert_eq!(result.selected().count(), 1);
    }

    #[test]
    fn full_selection_chooses_one_candidate_per_matched_eclass() {
        let first: ArrayExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: ArrayExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let expected: ArrayExpr =
            "(=> (not (= q p)) (= (Read Int Int (Write Int Int B p w) q) (Read Int Int B q)))"
                .parse()
                .unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        let first_id = egraph.add_expr(&first);
        let second_id = egraph.add_expr(&second);
        egraph.union(first_id, second_id);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            PreferB,
            &[("Int".into(), "Int".into())],
            ArrayInstantiationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        prepare_violations(&mut result, CandidateScope::AllCandidates);
        assert_eq!(
            result
                .selected()
                .map(|candidate| candidate.expression.clone())
                .collect::<Vec<_>>(),
            vec![expected]
        );
    }

    #[test]
    fn matched_eclass_ties_use_canonical_expression_order() {
        let first: ArrayExpr = "(Read Int Int (ConstArr Int Int z) i)".parse().unwrap();
        let second: ArrayExpr = "(Read Int Int (ConstArr Int Int z) j)".parse().unwrap();
        let expected: ArrayExpr = "(= (Read Int Int (ConstArr Int Int z) i) z)"
            .parse()
            .unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        let second_id = egraph.add_expr(&second);
        let first_id = egraph.add_expr(&first);
        egraph.union(first_id, second_id);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            ArrayInstantiationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        prepare_violations(&mut result, CandidateScope::AllCandidates);
        assert_eq!(
            result
                .selected()
                .map(|candidate| candidate.expression.clone())
                .collect::<Vec<_>>(),
            vec![expected]
        );
    }

    #[test]
    fn whole_instantiation_capture_keeps_all_candidates_and_marks_one_selected() {
        let first: ArrayExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: ArrayExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&first);
        egraph.add_expr(&second);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            PreferB,
            &[("Int".into(), "Int".into())],
            ArrayInstantiationOptions {
                candidate_catalog: two_write_candidate_catalog(),
                candidate_scope: CandidateScope::SourceGroundedOnly,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture: ArrayArtifactCapture {
                        decisions: true,
                        instantiation_provenance: true,
                        conflicts: false,
                    },
                    profiling: None,
                },
            },
        );

        assert!(result.selected().next().is_none());
        prepare_violations(&mut result, CandidateScope::SourceGroundedOnly);
        let abstract_instantiations = result
            .candidates
            .iter()
            .filter_map(|candidate| candidate.abstract_instantiation.as_ref())
            .collect::<Vec<_>>();
        assert!(abstract_instantiations.len() >= 2);
        assert_eq!(
            abstract_instantiations
                .iter()
                .filter(|record| record.was_selected)
                .count(),
            1
        );
        let selected_id = result
            .selected()
            .next()
            .unwrap()
            .provenance
            .abstract_instantiation_id();
        let selected_record = abstract_instantiations
            .iter()
            .find(|record| record.was_selected)
            .unwrap();
        assert_eq!(selected_record.abstract_instantiation_id, selected_id);
        assert!(!selected_record.substitution.is_empty());
        let decision_keys = result
            .candidates
            .iter()
            .flat_map(|candidate| candidate.decisions.iter())
            .map(|decision| decision.decision_key.clone())
            .collect::<HashSet<_>>();
        assert!(!decision_keys.is_empty());
        assert!(abstract_instantiations
            .iter()
            .flat_map(|record| record.decision_keys.iter())
            .all(|key| decision_keys.contains(key)));
    }

    #[test]
    fn decision_capture_does_not_change_selection() {
        fn run(artifact_capture: ArrayArtifactCapture) -> InstantiationBatch {
            let expr: RecExpr<ArrayLanguage> =
                "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
            let mut egraph = EGraph::<ArrayLanguage, ()>::default();
            egraph.add_expr(&expr);
            egraph.rebuild();

            let mut result = generate_array_instantiation_candidates(
                &egraph,
                ZeroCost,
                &[("Int".into(), "Int".into())],
                ArrayInstantiationOptions {
                    candidate_catalog: ArrayCandidateCatalog::default(),
                    candidate_scope: CandidateScope::AllCandidates,
                    refinement_step: 0,
                    selection_counts: FxHashMap::default(),
                    depth: 0,
                    instrumentation: ArrayInstantiationInstrumentation {
                        artifact_capture,
                        profiling: None,
                    },
                },
            );
            prepare_violations(&mut result, CandidateScope::AllCandidates);
            result
        }

        let compact = run(ArrayArtifactCapture::default());
        let recorded = run(ArrayArtifactCapture {
            decisions: true,
            instantiation_provenance: true,
            conflicts: false,
        });

        let compact_instantiations = compact
            .selected()
            .map(|candidate| candidate.expression.to_string())
            .collect::<Vec<_>>();
        let recorded_instantiations = recorded
            .selected()
            .map(|candidate| candidate.expression.to_string())
            .collect::<Vec<_>>();
        let compact_history = compact
            .selected()
            .flat_map(|candidate| candidate.selection_history.iter())
            .map(|decision| (&decision.decision_key, &decision.chosen_term_hash))
            .collect::<Vec<_>>();
        let recorded_history = recorded
            .selected()
            .flat_map(|candidate| candidate.selection_history.iter())
            .map(|decision| (&decision.decision_key, &decision.chosen_term_hash))
            .collect::<Vec<_>>();

        assert_eq!(compact_instantiations, recorded_instantiations);
        assert_eq!(compact_history, recorded_history);
        assert!(compact
            .candidates
            .iter()
            .all(|candidate| candidate.decisions.is_empty()));
        assert!(recorded
            .candidates
            .iter()
            .any(|candidate| !candidate.decisions.is_empty()));
        assert!(compact
            .candidates
            .iter()
            .all(|candidate| candidate.abstract_instantiation.is_none()));
        assert!(recorded
            .candidates
            .iter()
            .any(|candidate| candidate.abstract_instantiation.is_some()));
    }
}
