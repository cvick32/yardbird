//! Match enumeration, independent of representative extraction and scoring.

use std::{cell::RefCell, rc::Rc, time::Instant};

use crate::profiling::ArrayProfilingCollector;

use super::array_axioms::{ArrayLanguage, CompiledQuantifiedRule};

const INITIAL_ARRAY_MATCH_LIMIT: usize = 1_000;
const ARRAY_SEARCH_ROUNDS: usize = 15;
const BINDER_PAGE_SIZE: usize = 4_096;
// egg does not expose a resumable join. Bound prefix re-examination as well as
// retained matches: at most 16 queries (557,072 returned substitutions) per
// binder search pass, including lookahead. No budget establishes completeness.
const BINDER_SEARCH_LIMIT: usize = 65_536;

#[derive(Clone, Debug, Default)]
pub struct RuleSearchReport {
    /// Rules with another page available within the current search budget.
    pub continuable_rules: Vec<String>,
    /// Rules with unexamined matches after reaching their search budget.
    pub budget_exhausted_rules: Vec<String>,
    pub examined_substitutions: usize,
    pub rounds: usize,
}

pub(crate) struct RuleMatch {
    pub rule_index: usize,
    pub root: egg::Id,
    pub substitution: egg::Subst,
    pub model_violation_verified: bool,
}

#[derive(Default)]
pub(crate) struct MatchedRules {
    pub matches: Vec<RuleMatch>,
    pub report: RuleSearchReport,
}

#[derive(Default)]
pub(crate) struct BinderSearchCursor {
    offsets: Vec<usize>,
    complete: Vec<bool>,
}

impl BinderSearchCursor {
    pub fn can_continue(&self) -> bool {
        self.offsets
            .iter()
            .zip(&self.complete)
            .any(|(offset, complete)| !complete && *offset < BINDER_SEARCH_LIMIT)
    }
}

fn search<N: egg::Analysis<ArrayLanguage>>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    rule: &CompiledQuantifiedRule<N>,
    rule_index: usize,
    limit: usize,
    profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
) -> Vec<RuleMatch> {
    let start = Instant::now();
    let matches = rule.search_with_limit(egraph, limit);
    let count = matches.iter().map(|m| m.substs.len()).sum();
    if let Some(profiling) = profiling {
        let elapsed = start.elapsed();
        let mut profiling = profiling.borrow_mut();
        profiling.record_timing("rule_matching_total", elapsed);
        profiling.record_rule_search(rule.metadata().name(), matches.len(), count, elapsed);
    }
    matches
        .into_iter()
        .flat_map(|matched| {
            matched
                .substs
                .into_iter()
                .map(move |substitution| RuleMatch {
                    rule_index,
                    root: matched.eclass,
                    substitution,
                    model_violation_verified: false,
                })
        })
        .collect()
}

/// Preserve the historical array backoff range and ordering. Unlike binder
/// joins, array rules are not restricted to a 4,096-substitution prefix.
pub(crate) fn search_array_rules<N: egg::Analysis<ArrayLanguage>>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    rules: &[CompiledQuantifiedRule<N>],
    profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
) -> MatchedRules {
    let mut result = MatchedRules::default();
    let mut completed = vec![false; rules.len()];
    for round in 0..ARRAY_SEARCH_ROUNDS {
        result.report.rounds = round + 1;
        let limit = INITIAL_ARRAY_MATCH_LIMIT << round;
        for (index, rule) in rules.iter().enumerate() {
            if completed[index] {
                continue;
            }
            let matches = search(egraph, rule, index, limit + 1, profiling);
            result.report.examined_substitutions += matches.len();
            if matches.len() <= limit {
                completed[index] = true;
                result.matches.extend(matches);
            }
        }
        if completed.iter().all(|complete| *complete) {
            break;
        }
    }
    result.report.budget_exhausted_rules = rules
        .iter()
        .zip(completed)
        .filter(|(_, complete)| !complete)
        .map(|(rule, _)| rule.metadata().name().to_owned())
        .collect();
    result
}

/// Continue within the SAME model-equivalence graph. A new model must use a
/// new cursor; its e-class identities and matching order may have changed.
pub(crate) fn search_binder_page<N: egg::Analysis<ArrayLanguage>>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    rules: &[CompiledQuantifiedRule<N>],
    cursor: &mut BinderSearchCursor,
    profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
) -> MatchedRules {
    cursor.offsets.resize(rules.len(), 0);
    cursor.complete.resize(rules.len(), false);
    let mut result = MatchedRules::default();
    result.report.rounds = 1;
    for (index, rule) in rules.iter().enumerate() {
        if cursor.complete[index] {
            continue;
        }
        let offset = cursor.offsets[index];
        if offset < BINDER_SEARCH_LIMIT {
            let end = (offset + BINDER_PAGE_SIZE).min(BINDER_SEARCH_LIMIT);
            // Always ask for a lookahead, including at the work limit.
            let matches = search(egraph, rule, index, end + 1, profiling);
            result.report.examined_substitutions += matches.len();
            cursor.complete[index] = matches.len() <= end;
            result
                .matches
                .extend(matches.into_iter().skip(offset).take(end - offset));
            cursor.offsets[index] = end;
        }
        if !cursor.complete[index] {
            let remaining = if cursor.offsets[index] < BINDER_SEARCH_LIMIT {
                &mut result.report.continuable_rules
            } else {
                &mut result.report.budget_exhausted_rules
            };
            remaining.push(rule.metadata().name().to_owned());
        }
    }
    result
}
