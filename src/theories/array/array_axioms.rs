use std::{cell::RefCell, collections::HashSet, fmt, rc::Rc, time::Instant};

use egg::*;
use rustc_hash::FxHashMap;
use smt2parser::concrete::{Constant, Identifier, QualIdentifier, Symbol as SmtSymbol, Term};

use crate::{
    auxiliary_synthesis::ArrayConflictRecord,
    cost_functions::YardbirdCostFunction,
    instantiation_provenance::InstantiationProvenance,
    problem_context::ArrayCandidateCatalog,
    profiling::ArrayProfilingCollector,
    theories::array::{
        array_conflict_scheduler::{
            ArrayArtifactCapture, ArrayConflictScheduler, ArrayConflictSchedulerOptions,
        },
        array_instantiation_ranker::{
            ArrayInstantiationCandidate, ArrayInstantiationRanker, CompleteCostInstantiationRanker,
        },
        array_term_extractor::{ArrayTermExtractor, ArrayTermExtractorOptions},
        candidate_scope::CandidateScope,
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

/// One complete array-axiom candidate with the exact provenance selected by the
/// scheduler. Keeping the expression and provenance together prevents later
/// stages from trying to reconstruct identity from a non-unique term hash.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArrayAxiomInstantiation {
    pub expression: ArrayExpr,
    pub provenance: InstantiationProvenance,
}

impl PartialEq<ArrayExpr> for ArrayAxiomInstantiation {
    fn eq(&self, other: &ArrayExpr) -> bool {
        &self.expression == other
    }
}

impl fmt::Display for ArrayAxiomInstantiation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.expression.fmt(formatter)
    }
}

pub struct ArraySaturationResult {
    pub instantiations: Vec<ArrayAxiomInstantiation>,
    pub const_instantiations: Vec<ArrayAxiomInstantiation>,
    pub conflicts: Vec<ArrayConflictRecord>,
    pub decisions: Vec<crate::training::DecisionRecord>,
    pub abstract_instantiations: Vec<crate::training::AbstractInstantiationRecord>,
    pub selection_history_decisions: Vec<(String, String)>,
    pub instantiation_decision_keys: Vec<Vec<String>>,
}

pub struct ArraySaturationInstrumentation {
    pub artifact_capture: ArrayArtifactCapture,
    pub profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

pub struct ArraySaturationOptions {
    pub candidate_catalog: ArrayCandidateCatalog,
    pub candidate_scope: CandidateScope,
    /// Complete abstract instances rejected by the caller for this e-graph
    /// stage. Matching must continue past these candidates.
    pub excluded_instantiations: HashSet<ArrayExpr>,
    pub refinement_step: u32,
    pub selection_counts: FxHashMap<String, u32>,
    pub depth: u16,
    pub instrumentation: ArraySaturationInstrumentation,
}

fn egraph_node_count<N>(egraph: &EGraph<ArrayLanguage, N>) -> usize
where
    N: Analysis<ArrayLanguage>,
{
    egraph.classes().map(|class| class.nodes.len()).sum()
}

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
    array_types: &[(String, String)],
    options: ArraySaturationOptions,
) -> ArraySaturationResult
where
    N: Analysis<ArrayLanguage> + Default + 'static,
    CF: YardbirdCostFunction<ArrayLanguage> + 'static,
{
    saturate_with_array_types_and_ranker(
        egraph,
        cost_fn,
        array_types,
        options,
        &CompleteCostInstantiationRanker,
    )
}

pub fn saturate_with_array_types_and_ranker<CF, N>(
    egraph: &mut EGraph<ArrayLanguage, N>,
    cost_fn: CF,
    array_types: &[(String, String)],
    options: ArraySaturationOptions,
    instantiation_ranker: &dyn ArrayInstantiationRanker,
) -> ArraySaturationResult
where
    N: Analysis<ArrayLanguage> + Default + 'static,
    CF: YardbirdCostFunction<ArrayLanguage> + 'static,
{
    // This function is the extraction seam for a future saturation module.
    // Keep eligibility, term cost, and whole-instantiation ranking behind their
    // existing interfaces if the Runner/Scheduler orchestration moves.
    let ArraySaturationOptions {
        candidate_catalog,
        candidate_scope,
        excluded_instantiations,
        refinement_step,
        selection_counts,
        depth,
        instrumentation,
    } = options;
    let ArraySaturationInstrumentation {
        artifact_capture,
        profiling,
    } = instrumentation;
    let taken_egraph = std::mem::take(egraph);
    if let Some(profiling) = &profiling {
        profiling.borrow_mut().set_egraph_before_saturation(
            taken_egraph.number_of_classes(),
            egraph_node_count(&taken_egraph),
        );
    }
    let scheduler_cost_fn = cost_fn.clone();
    let mut complete_ranking_cost_fn = cost_fn.clone();
    let extractor_start = Instant::now();
    let extractor = ArrayTermExtractor::new(
        &taken_egraph,
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
    let scheduler = ArrayConflictScheduler::new(
        BackoffScheduler::default(),
        scheduler_cost_fn,
        extractor,
        ArrayConflictSchedulerOptions {
            excluded_instantiations,
            refinement_step,
            depth,
            artifact_capture,
            profiling: profiling.clone(),
        },
    );
    let instantiations = scheduler.instantiations();
    let const_instantiations = scheduler.instantiations_w_constants();
    let conflicts = scheduler.conflicts();
    let decisions = scheduler.decisions();
    let abstract_instantiations = scheduler.abstract_instantiations();
    let selection_history_decisions = scheduler.selection_history_decisions();
    let instantiation_decision_keys = scheduler.instantiation_decision_keys();
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
                    log::debug!("ClassID={:?}, Node: {:?}", class.id, node);
                }
            }
        }
    }

    let runner_start = Instant::now();
    let mut runner = Runner::default()
        .with_egraph(taken_egraph)
        .with_scheduler(scheduler)
        .run(&axioms);
    if let Some(profiling) = &profiling {
        profiling
            .borrow_mut()
            .record_timing("runner_total", runner_start.elapsed());
        profiling.borrow_mut().set_egraph_after_saturation(
            runner.egraph.number_of_classes(),
            egraph_node_count(&runner.egraph),
            runner.iterations.len(),
        );
    }

    *egraph = std::mem::take(&mut runner.egraph);
    drop(runner);

    let all_regular_insts = Rc::into_inner(instantiations).unwrap().into_inner();
    let all_const_insts = Rc::into_inner(const_instantiations).unwrap().into_inner();
    let all_conflicts = Rc::into_inner(conflicts).unwrap().into_inner();
    let all_decisions = Rc::into_inner(decisions).unwrap().into_inner();
    let all_abstract_instantiations = Rc::into_inner(abstract_instantiations)
        .unwrap()
        .into_inner();
    let all_selection_history_decisions = Rc::into_inner(selection_history_decisions)
        .unwrap()
        .into_inner()
        .into_iter()
        .map(|decision| (decision.decision_key, decision.chosen_term_hash))
        .collect::<Vec<_>>();
    let all_instantiation_decision_keys = Rc::into_inner(instantiation_decision_keys)
        .unwrap()
        .into_inner();
    let (
        final_insts,
        final_const_insts,
        final_conflicts,
        final_decisions,
        final_abstract_instantiations,
        final_selection_history_decisions,
        final_instantiation_decision_keys,
    ) = if candidate_scope.selected_instantiation_limit().is_none() {
        (
            all_regular_insts,
            all_const_insts,
            all_conflicts,
            all_decisions,
            all_abstract_instantiations,
            all_selection_history_decisions,
            all_instantiation_decision_keys
                .into_iter()
                .map(|(_, keys)| keys)
                .collect(),
        )
    } else {
        let candidates = all_regular_insts
            .iter()
            .map(|instantiation| (instantiation, false))
            .chain(
                all_const_insts
                    .iter()
                    .map(|instantiation| (instantiation, true)),
            )
            .enumerate()
            .map(
                |(discovery_order, (instantiation, is_const_or_high_cost))| {
                    ArrayInstantiationCandidate {
                        expression: instantiation.expression.clone(),
                        complete_cost: complete_ranking_cost_fn.cost_rec(&instantiation.expression),
                        is_const_or_high_cost,
                        discovery_order,
                    }
                },
            )
            .collect::<Vec<_>>();
        let selected = instantiation_ranker
            .select(
                &candidates,
                candidate_scope.selected_instantiation_limit().unwrap(),
            )
            .into_iter()
            .next()
            .map(|index| {
                let candidate = &candidates[index];
                let instantiation = if candidate.is_const_or_high_cost {
                    all_const_insts.get(index.saturating_sub(all_regular_insts.len()))
                } else {
                    all_regular_insts.get(index)
                }
                .expect("ranker returned a valid candidate index")
                .clone();
                (instantiation, candidate.is_const_or_high_cost)
            });
        let selected_abstract_id = selected.as_ref().map(|(instantiation, _)| {
            instantiation
                .provenance
                .abstract_instantiation_id()
                .to_string()
        });
        let selected_decision_keys = selected_abstract_id
            .as_ref()
            .and_then(|selected_id| {
                all_instantiation_decision_keys
                    .iter()
                    .find(|(candidate_id, _)| candidate_id == selected_id)
                    .map(|(_, keys)| keys.clone())
            })
            .unwrap_or_default();
        let selected_decision_key_set = selected_decision_keys
            .iter()
            .cloned()
            .collect::<HashSet<_>>();
        let mut selected_conflicts = all_conflicts;
        let mut candidate_abstract_instantiations = all_abstract_instantiations;
        let mut selected_history = all_selection_history_decisions;
        if let Some(selected_id) = selected_abstract_id.as_ref() {
            selected_conflicts.retain(|record| &record.abstract_instantiation_id == selected_id);
            for record in &mut candidate_abstract_instantiations {
                record.was_selected = &record.abstract_instantiation_id == selected_id;
            }
            selected_history.retain(|(key, _)| selected_decision_key_set.contains(key));
        } else {
            selected_conflicts.clear();
            for record in &mut candidate_abstract_instantiations {
                record.was_selected = false;
            }
            selected_history.clear();
        }
        let selected_instantiation_decision_keys = selected_abstract_id
            .as_ref()
            .map(|_| vec![selected_decision_keys])
            .unwrap_or_default();
        let (selected_regular, selected_const) = match selected {
            Some((instantiation, true)) => (vec![], vec![instantiation]),
            Some((instantiation, false)) => (vec![instantiation], vec![]),
            None => (vec![], vec![]),
        };
        (
            selected_regular,
            selected_const,
            selected_conflicts,
            all_decisions,
            candidate_abstract_instantiations,
            selected_history,
            selected_instantiation_decision_keys,
        )
    };

    #[cfg(debug_assertions)]
    {
        log::debug!("=== FINAL INSTANTIATIONS ===");
        log::debug!("Regular: {}", final_insts.len());
        for (i, inst) in final_insts.iter().enumerate() {
            log::debug!("  [{}]: {}", i, inst);
        }
        log::debug!("Const: {}", final_const_insts.len());
        for (i, inst) in final_const_insts.iter().enumerate() {
            log::debug!("  [{}]: {}", i, inst);
        }
        log::debug!("============================\n");
    }

    ArraySaturationResult {
        instantiations: final_insts,
        const_instantiations: final_const_insts,
        conflicts: final_conflicts,
        decisions: final_decisions,
        abstract_instantiations: final_abstract_instantiations,
        selection_history_decisions: final_selection_history_decisions,
        instantiation_decision_keys: final_instantiation_decision_keys,
    }
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
            Term::Forall { .. } => None,
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
    use super::*;
    use crate::cost_functions::YardbirdCostFunction;
    use rustc_hash::FxHashMap;
    use smt2parser::vmt::ReadsAndWrites;

    #[derive(Clone)]
    struct ZeroCost;

    #[derive(Clone)]
    struct HighCost {
        terms: Vec<ArrayExpr>,
    }

    #[derive(Clone)]
    struct PreferB;

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

    impl egg::CostFunction<ArrayLanguage> for HighCost {
        type Cost = u32;

        fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            enode.fold(100, |sum, child| sum.saturating_add(costs(child)))
        }
    }

    impl YardbirdCostFunction<ArrayLanguage> for HighCost {
        fn get_string_terms(&self) -> Vec<String> {
            self.terms.iter().map(ToString::to_string).collect()
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }

        fn get_parsed_terms(&self) -> Vec<ArrayExpr> {
            self.terms.clone()
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

        let result = saturate_with_array_types(
            &mut egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            ArraySaturationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                excluded_instantiations: HashSet::new(),
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArraySaturationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert_eq!(result.instantiations.len(), 1);
        let instantiation = &result.instantiations[0];
        assert!(instantiation.to_string().starts_with("(=> "));

        let term = expr_to_term(instantiation.expression.clone()).to_string();
        assert_eq!(
            term,
            "(=> (not (= 1 0)) (= (Read_Int_Int (Write_Int_Int A 0 0) 1) (Read_Int_Int A 1)))"
        );
    }

    #[test]
    fn saturation_preserves_the_egraph_for_staged_expansion() {
        let expr: RecExpr<ArrayLanguage> =
            "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&expr);
        egraph.rebuild();

        let _ = saturate_with_array_types(
            &mut egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            ArraySaturationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                excluded_instantiations: HashSet::new(),
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArraySaturationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert!(
            egraph.lookup_expr(&expr).is_some(),
            "saturation must return ownership of the e-graph so a later builder stage can widen it"
        );
    }

    #[test]
    fn source_only_saturation_does_not_emit_model_derived_join() {
        init();
        let expr: RecExpr<ArrayLanguage> =
            "(Read Int Int (Write Int Int A i 137) j)".parse().unwrap();

        let run = |scope| {
            let mut egraph = EGraph::<ArrayLanguage, ()>::default();
            egraph.add_expr(&expr);
            egraph.rebuild();
            saturate_with_array_types(
                &mut egraph,
                ZeroCost,
                &[("Int".into(), "Int".into())],
                ArraySaturationOptions {
                    candidate_catalog: ArrayCandidateCatalog::default(),
                    candidate_scope: scope,
                    excluded_instantiations: HashSet::new(),
                    refinement_step: 0,
                    selection_counts: FxHashMap::default(),
                    depth: 0,
                    instrumentation: ArraySaturationInstrumentation {
                        artifact_capture: ArrayArtifactCapture::default(),
                        profiling: None,
                    },
                },
            )
        };

        let cone = run(CandidateScope::SourceGroundedOnly);
        let full = run(CandidateScope::SourceThenDerived);

        assert!(cone.instantiations.is_empty());
        assert!(cone.const_instantiations.is_empty());
        assert_eq!(full.instantiations.len(), 1);
    }

    #[test]
    fn cone_saturation_emits_only_one_high_cost_candidate() {
        let first: ArrayExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: ArrayExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let source_terms = [
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
        .collect::<Vec<_>>();
        let parsed_terms = source_terms
            .iter()
            .filter_map(|term| term.parse::<Term>().ok())
            .filter_map(translate_term)
            .collect::<Vec<_>>();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&first);
        egraph.add_expr(&second);
        egraph.rebuild();

        let result = saturate_with_array_types(
            &mut egraph,
            HighCost {
                terms: parsed_terms,
            },
            &[("Int".into(), "Int".into())],
            ArraySaturationOptions {
                candidate_catalog: ArrayCandidateCatalog {
                    source_grounded: crate::problem_context::ArrayCandidatePool {
                        terms: source_terms,
                        reads_and_writes: ReadsAndWrites::from(
                            std::collections::HashSet::new(),
                            std::collections::HashSet::from([
                                ("A".to_string(), "i".to_string(), "v".to_string()),
                                ("B".to_string(), "p".to_string(), "w".to_string()),
                            ]),
                        ),
                    },
                    derived: crate::problem_context::ArrayCandidatePool::default(),
                },
                candidate_scope: CandidateScope::SourceGroundedOnly,
                excluded_instantiations: HashSet::new(),
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArraySaturationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert!(result.instantiations.is_empty());
        assert_eq!(result.const_instantiations.len(), 1);
    }

    #[test]
    fn saturation_skips_an_excluded_candidate_and_selects_the_next_violation() {
        let first: ArrayExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: ArrayExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let known: ArrayExpr =
            "(=> (not (= j i)) (= (Read Int Int (Write Int Int A i v) j) (Read Int Int A j)))"
                .parse()
                .unwrap();
        let expected: ArrayExpr =
            "(=> (not (= q p)) (= (Read Int Int (Write Int Int B p w) q) (Read Int Int B q)))"
                .parse()
                .unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&first);
        egraph.add_expr(&second);
        egraph.rebuild();

        let result = saturate_with_array_types(
            &mut egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            ArraySaturationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                excluded_instantiations: std::collections::HashSet::from([known]),
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArraySaturationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert_eq!(result.instantiations, vec![expected]);
    }

    #[test]
    fn saturation_ranks_complete_violations_across_rewrite_matches() {
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

        let result = saturate_with_array_types(
            &mut egraph,
            PreferB,
            &[("Int".into(), "Int".into())],
            ArraySaturationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::SourceThenDerived,
                excluded_instantiations: HashSet::new(),
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArraySaturationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert_eq!(result.instantiations, vec![expected]);
    }

    #[test]
    fn whole_instantiation_capture_keeps_all_candidates_and_marks_one_selected() {
        let first: ArrayExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: ArrayExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&first);
        egraph.add_expr(&second);
        egraph.rebuild();

        let result = saturate_with_array_types(
            &mut egraph,
            PreferB,
            &[("Int".into(), "Int".into())],
            ArraySaturationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::SourceThenDerived,
                excluded_instantiations: HashSet::new(),
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArraySaturationInstrumentation {
                    artifact_capture: ArrayArtifactCapture {
                        decisions: true,
                        instantiation_provenance: true,
                        conflicts: false,
                    },
                    profiling: None,
                },
            },
        );

        assert!(result.abstract_instantiations.len() >= 2);
        assert_eq!(
            result
                .abstract_instantiations
                .iter()
                .filter(|record| record.was_selected)
                .count(),
            1
        );
        let selected_id = result.instantiations[0]
            .provenance
            .abstract_instantiation_id();
        let selected_record = result
            .abstract_instantiations
            .iter()
            .find(|record| record.was_selected)
            .unwrap();
        assert_eq!(selected_record.abstract_instantiation_id, selected_id);
        assert!(!selected_record.substitution.is_empty());
        assert!(!result.decisions.is_empty());
        let decision_keys = result
            .decisions
            .iter()
            .map(|decision| decision.decision_key.clone())
            .collect::<HashSet<_>>();
        assert_eq!(decision_keys.len(), result.decisions.len());
        assert!(result
            .abstract_instantiations
            .iter()
            .flat_map(|record| record.decision_keys.iter())
            .all(|key| decision_keys.contains(key)));
    }

    #[test]
    fn saturation_accepts_a_programmatic_complete_instantiation_ranker() {
        use crate::theories::array::array_instantiation_ranker::DiscoveryOrderInstantiationRanker;

        let first: ArrayExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: ArrayExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let expected_first: ArrayExpr =
            "(=> (not (= j i)) (= (Read Int Int (Write Int Int A i v) j) (Read Int Int A j)))"
                .parse()
                .unwrap();
        let mut egraph = EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&first);
        egraph.add_expr(&second);
        egraph.rebuild();

        let result = saturate_with_array_types_and_ranker(
            &mut egraph,
            PreferB,
            &[("Int".into(), "Int".into())],
            ArraySaturationOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::SourceThenDerived,
                excluded_instantiations: HashSet::new(),
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: ArraySaturationInstrumentation {
                    artifact_capture: ArrayArtifactCapture::default(),
                    profiling: None,
                },
            },
            &DiscoveryOrderInstantiationRanker,
        );

        assert_eq!(result.instantiations, vec![expected_first]);
    }

    #[test]
    fn decision_capture_does_not_change_saturation_choices() {
        fn run(artifact_capture: ArrayArtifactCapture) -> ArraySaturationResult {
            let expr: RecExpr<ArrayLanguage> =
                "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
            let mut egraph = EGraph::<ArrayLanguage, ()>::default();
            egraph.add_expr(&expr);
            egraph.rebuild();

            saturate_with_array_types(
                &mut egraph,
                ZeroCost,
                &[("Int".into(), "Int".into())],
                ArraySaturationOptions {
                    candidate_catalog: ArrayCandidateCatalog::default(),
                    candidate_scope: CandidateScope::AllCandidates,
                    excluded_instantiations: HashSet::new(),
                    refinement_step: 0,
                    selection_counts: FxHashMap::default(),
                    depth: 0,
                    instrumentation: ArraySaturationInstrumentation {
                        artifact_capture,
                        profiling: None,
                    },
                },
            )
        }

        let compact = run(ArrayArtifactCapture::default());
        let recorded = run(ArrayArtifactCapture {
            decisions: true,
            instantiation_provenance: true,
            conflicts: false,
        });

        let compact_instantiations = compact
            .instantiations
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let recorded_instantiations = recorded
            .instantiations
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();

        assert_eq!(compact_instantiations, recorded_instantiations);
        assert_eq!(
            compact.selection_history_decisions,
            recorded.selection_history_decisions
        );
        assert_eq!(
            compact.instantiation_decision_keys,
            recorded.instantiation_decision_keys
        );
        assert!(compact.decisions.is_empty());
        assert!(!recorded.decisions.is_empty());
        assert!(compact.abstract_instantiations.is_empty());
        assert!(!recorded.abstract_instantiations.is_empty());
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
