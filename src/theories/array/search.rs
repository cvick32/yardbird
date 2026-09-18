//! Array search batches using the policy-provided backoff allowance.
use std::{cell::RefCell, rc::Rc};

use crate::profiling::RefinementProfilingCollector;

use crate::rule_matching::compiled_rule::CompiledQuantifiedRule;
use crate::terms::language::TermLanguage;

use crate::rule_matching::search::{search, MatchedRules};
/// Preserve the historical array backoff range and ordering. Unlike binder
/// joins, array rules are not restricted to a binder-sized page.
pub(crate) fn search_array_rules<N: egg::Analysis<TermLanguage>, M>(
    egraph: &egg::EGraph<TermLanguage, N>,
    rules: &[CompiledQuantifiedRule<N, M>],
    allowance: &crate::policy::effort::WorkAllowance,
    profiling: &Option<Rc<RefCell<RefinementProfilingCollector>>>,
) -> MatchedRules {
    let mut result = MatchedRules::default();
    let mut completed = vec![false; rules.len()];
    for round in 0..allowance.array_rounds {
        result.report.rounds = round + 1;
        let limit = allowance.array_initial_limit << round;
        for (index, rule) in rules.iter().enumerate() {
            if completed[index] {
                continue;
            }
            let (matches, examined) = search(egraph, rule, index, limit + 1, profiling);
            result.report.examined_substitutions += examined;
            if matches.len() <= limit {
                completed[index] = true;
                result.matches.extend(matches);
            }
        }
        if completed.iter().all(|complete| *complete) {
            break;
        }
    }
    result.report.returned_substitutions = result.matches.len();
    result.report.budget_exhausted_rules = rules
        .iter()
        .zip(completed)
        .filter(|(_, complete)| !complete)
        .map(|(rule, _)| rule.metadata().name().to_owned())
        .collect();
    result
}

use crate::policy::term_selection::YardbirdCostFunction;
use crate::rule_matching::{
    candidate::InstantiationBatch,
    candidate_builder::{instantiate_quantified_matches, CandidateDemand, InstantiationOptions},
};
use egg::{Analysis, EGraph};

/// Shared matching, representative extraction and complete-instance scoring.
pub(crate) fn generate_quantified_candidates<CF, N, M>(
    egraph: &EGraph<TermLanguage, N>,
    cost_fn: CF,
    rules: &[CompiledQuantifiedRule<N, M>],
    options: InstantiationOptions,
    demand: Option<CandidateDemand<'_>>,
) -> anyhow::Result<InstantiationBatch>
where
    N: Analysis<TermLanguage> + 'static,
    CF: YardbirdCostFunction<TermLanguage> + 'static,
{
    let matched = search_array_rules(
        egraph,
        rules,
        &options.search_allowance,
        &options.instrumentation.profiling,
    );
    instantiate_quantified_matches(egraph, || cost_fn, rules, options, matched, demand, None)
}
