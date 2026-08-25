//! E-graph candidate search and cost ranking for quantified transition guards.

use std::collections::HashSet;

use egg::Searcher;
use smt2parser::concrete::Term;

use crate::{
    cost_functions::YardbirdCostFunction,
    instantiation_provenance::InstantiationProvenance,
    problem_context::ProblemContext,
    quantified_rule::TransitionGuardRule,
    theories::array::{
        array_axioms::{expr_to_term, translate_term, ArrayExpr, ArrayLanguage},
        array_term_extractor::{ArrayTermExtractor, CandidateOrigin},
    },
};

/// One ranked ground transition-guard instance in the current model.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TransitionGuardInstance {
    pub candidate: ArrayExpr,
    pub formula: Term,
    pub expression: ArrayExpr,
    pub cost: u32,
    pub provenance: InstantiationProvenance,
}

/// Finds ground terms occupying an array-index slot of the guard binder's
/// sort. For German this turns the many `client`-indexed reads and writes into
/// the candidate pool for `I:client`.
struct ArrayIndexCandidateSearcher {
    candidate_var: egg::Var,
    patterns: [egg::Pattern<ArrayLanguage>; 2],
}

impl ArrayIndexCandidateSearcher {
    fn compile(rule: &TransitionGuardRule) -> Option<Self> {
        let [(binder, sort)] = rule.bound_variables() else {
            return None;
        };
        let index_sort = ArrayLanguage::sort_to_name(sort);
        if !is_supported_negative_read_guard(rule.body(), &binder.0, &index_sort) {
            return None;
        }

        let candidate_var = "?guard_candidate".parse().unwrap();
        let read = format!(
            "(Read {index_sort} ?guard_read_value_sort ?guard_read_array ?guard_candidate)"
        )
        .parse()
        .unwrap();
        let write = format!(
            "(Write {index_sort} ?guard_write_value_sort ?guard_write_array ?guard_candidate ?guard_write_value)"
        )
        .parse()
        .unwrap();
        Some(Self {
            candidate_var,
            patterns: [read, write],
        })
    }

    fn search<N>(&self, egraph: &egg::EGraph<ArrayLanguage, N>) -> Vec<egg::Id>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let mut candidates = HashSet::new();
        for pattern in &self.patterns {
            for matched in pattern.search(egraph) {
                for substitution in matched.substs {
                    candidates.insert(egraph.find(substitution[self.candidate_var]));
                }
            }
        }
        let mut candidates = candidates.into_iter().collect::<Vec<_>>();
        candidates.sort();
        candidates
    }
}

pub fn supports_transition_guard(rule: &TransitionGuardRule) -> bool {
    ArrayIndexCandidateSearcher::compile(rule).is_some()
}

fn is_supported_negative_read_guard(body: &Term, binder: &str, index_sort: &str) -> bool {
    let Term::Application {
        qual_identifier,
        arguments,
    } = body
    else {
        return false;
    };
    if qual_identifier.get_name() != "not" || arguments.len() != 1 {
        return false;
    }
    let Term::Application {
        qual_identifier,
        arguments,
    } = &arguments[0]
    else {
        return false;
    };
    let Some(array_sorts) = qual_identifier
        .get_name()
        .strip_prefix("Read_")
        .map(str::to_owned)
    else {
        return false;
    };
    let Some((read_index_sort, _)) = array_sorts.split_once('_') else {
        return false;
    };
    arguments.len() == 2
        && read_index_sort == index_sort
        && matches!(&arguments[1], Term::QualIdentifier(identifier) if identifier.get_name() == binder)
}

fn contains_symbol(expression: &ArrayExpr, symbol: &str) -> bool {
    expression.as_ref().iter().any(
        |node| matches!(node, ArrayLanguage::Symbol(candidate) if candidate.as_str() == symbol),
    )
}

/// Rank the currently visible ground instances that violate one supported
/// transition guard in the current model.
pub fn rank_violated_transition_guard_instances<CF, N>(
    rule: &TransitionGuardRule,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    extractor: &ArrayTermExtractor<CF>,
    mut cost_function: CF,
    depth: u16,
    smt: &dyn ProblemContext,
) -> Vec<TransitionGuardInstance>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
    N: egg::Analysis<ArrayLanguage>,
{
    let Some(searcher) = ArrayIndexCandidateSearcher::compile(rule) else {
        return vec![];
    };
    let [(binder, _)] = rule.bound_variables() else {
        unreachable!("supported transition guards have one binder")
    };
    let binder_name = binder.0.as_str();
    let mut seen_formulas = HashSet::new();
    let mut instances = Vec::new();

    for candidate_eclass in searcher.search(egraph) {
        let (candidate, origin) = extractor.extract_for_decision_with_origin(
            egraph,
            candidate_eclass,
            rule.metadata().name(),
            0,
        );
        if extractor.requires_source_grounded_candidates() && origin == CandidateOrigin::Derived {
            continue;
        }
        if contains_symbol(&candidate, binder_name) {
            continue;
        }
        let Some(unframed_formula) = rule.ground_formula(expr_to_term(candidate.clone())) else {
            continue;
        };

        for frame in 0..depth {
            let Some(formula) = smt.frame_transition_formula(unframed_formula.clone(), frame)
            else {
                continue;
            };
            if !seen_formulas.insert(formula.to_string()) {
                continue;
            }
            let Some(expression) = translate_term(formula.clone()) else {
                continue;
            };
            let cost = cost_function.cost_rec(&expression);
            let provenance = InstantiationProvenance::new(
                format!(
                    "{}:{}",
                    rule.metadata().name(),
                    crate::training::canonical_term_hash(&expression)
                ),
                vec![(binder_name.to_string(), expr_to_term(candidate.clone()))],
            );
            match smt.eval_to_string(&formula) {
                Ok(value) if value.trim() == "false" => {}
                Ok(_) => continue,
                Err(error) => {
                    log::warn!(
                        "Could not evaluate transition guard {}: {error:#}",
                        rule.metadata().name()
                    );
                    continue;
                }
            }
            instances.push(TransitionGuardInstance {
                candidate: candidate.clone(),
                formula,
                expression,
                cost,
                provenance,
            });
        }
    }

    instances.sort_by(|left, right| {
        left.cost
            .cmp(&right.cost)
            .then_with(|| left.formula.to_string().cmp(&right.formula.to_string()))
    });
    instances
}
