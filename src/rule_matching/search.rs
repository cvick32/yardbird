//! Match enumeration, independent of representative extraction and scoring.

use std::{cell::RefCell, rc::Rc, time::Instant};

use crate::profiling::RefinementProfilingCollector;

use crate::rule_matching::compiled_rule::CompiledQuantifiedRule;
use crate::terms::language::TermLanguage;

#[derive(Clone, Debug, Default)]
pub struct RuleSearchReport {
    /// Rules with another page available within the current search budget.
    pub continuable_rules: Vec<String>,
    /// Rules with unexamined matches after reaching their search budget.
    pub budget_exhausted_rules: Vec<String>,
    /// Matcher output examined, including replayed prefixes and lookahead.
    pub examined_substitutions: usize,
    /// Fresh page substitutions passed on for grounding, excluding replay.
    pub returned_substitutions: usize,
    pub cache_hit: bool,
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

pub(crate) fn search<N: egg::Analysis<TermLanguage>, M>(
    egraph: &egg::EGraph<TermLanguage, N>,
    rule: &CompiledQuantifiedRule<N, M>,
    rule_index: usize,
    limit: usize,
    profiling: &Option<Rc<RefCell<RefinementProfilingCollector>>>,
) -> (Vec<RuleMatch>, usize) {
    let start = Instant::now();
    let matches = rule.search_with_limit(egraph, limit);
    let count = matches.iter().map(|m| m.substs.len()).sum::<usize>();
    if let Some(profiling) = profiling {
        let elapsed = start.elapsed();
        let mut profiling = profiling.borrow_mut();
        profiling.record_timing("rule_matching_total", elapsed);
        profiling.record_rule_search(rule.metadata().name(), matches.len(), count, elapsed);
    }
    let found = matches
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
        .collect();
    (found, count)
}
