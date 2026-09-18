//! Match enumeration, independent of representative extraction and scoring.

use std::{cell::RefCell, rc::Rc, time::Instant};

use crate::profiling::ArrayProfilingCollector;

use crate::instantiation::{engine::CompiledQuantifiedRule, language::TermLanguage};

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

#[derive(Clone, Copy, Debug)]
enum BinderRuleCursor {
    Pending { offset: usize },
    Complete,
    Exhausted,
}

#[derive(Default)]
pub(crate) struct BinderSearchCursor {
    rules: Vec<BinderRuleCursor>,
    next_rule: usize,
}

impl BinderSearchCursor {
    pub(crate) fn starting_at(next_rule: usize) -> Self {
        Self {
            next_rule,
            ..Self::default()
        }
    }

    pub(crate) fn pending_rules(&self, count: usize) -> Vec<usize> {
        (0..count)
            .filter(|i| {
                self.rules
                    .get(*i)
                    .is_none_or(|r| matches!(r, BinderRuleCursor::Pending { .. }))
            })
            .collect()
    }
    #[cfg(test)]
    pub fn can_continue(&self) -> bool {
        self.rules
            .iter()
            .any(|rule| matches!(rule, BinderRuleCursor::Pending { .. }))
    }
}

fn search<N: egg::Analysis<TermLanguage>>(
    egraph: &egg::EGraph<TermLanguage, N>,
    rule: &CompiledQuantifiedRule<N>,
    rule_index: usize,
    limit: usize,
    profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
) -> (Vec<RuleMatch>, usize) {
    let start = Instant::now();
    let matches = rule.search_with_limit(egraph, limit);
    let count = matches.iter().map(|m| m.substs.len()).sum::<usize>();
    if let Some(profiling) = profiling {
        let elapsed = start.elapsed();
        let mut profiling = profiling.borrow_mut();
        profiling.record_timing("rule_matching_total", elapsed);
        profiling.record_rule_search(rule.metadata().name(), matches.len(), count, elapsed);
        if rule.uses_violation_plan() {
            profiling.record_quantifier_counter(
                rule.metadata().name(),
                "violation_plan_searches",
                1,
            );
            profiling.record_quantifier_counter(
                rule.metadata().name(),
                "violation_plan_substitutions_returned",
                count as u64,
            );
        }
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

/// Preserve the historical array backoff range and ordering. Unlike binder
/// joins, array rules are not restricted to a binder-sized page.
pub(crate) fn search_array_rules<N: egg::Analysis<TermLanguage>>(
    egraph: &egg::EGraph<TermLanguage, N>,
    rules: &[CompiledQuantifiedRule<N>],
    allowance: &crate::policy::effort::WorkAllowance,
    profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
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

fn search_binder_rule_page<N: egg::Analysis<TermLanguage>>(
    egraph: &egg::EGraph<TermLanguage, N>,
    rule: &CompiledQuantifiedRule<N>,
    rule_index: usize,
    cursor: &mut BinderRuleCursor,
    allowance: &crate::policy::effort::WorkAllowance,
    profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
) -> MatchedRules {
    let BinderRuleCursor::Pending { offset } = *cursor else {
        return MatchedRules::default();
    };

    if rule.is_direct_binder_instance() {
        // Every argument is already symbolic and ground. In particular the
        // helper application need not exist in this model's term vocabulary.
        *cursor = BinderRuleCursor::Complete;
        if let Some(profiling) = profiling {
            profiling
                .borrow_mut()
                .add_counter("input_binder_direct_instances", 1);
        }
        return MatchedRules {
            matches: vec![RuleMatch {
                rule_index,
                // Binder candidates are grouped by rule; no equality root is
                // consulted when grounding their complete Boolean formula.
                root: egraph
                    .classes()
                    .next()
                    .expect("prepared binder graph is nonempty")
                    .id,
                substitution: egg::Subst::default(),
                model_violation_verified: false,
            }],
            report: RuleSearchReport {
                returned_substitutions: 1,
                ..Default::default()
            },
        };
    }

    let end = offset
        .saturating_add(allowance.binder_page_size)
        .min(allowance.binder_search_limit);
    let (matches, examined_substitutions) = search(egraph, rule, rule_index, end + 1, profiling);

    *cursor = if examined_substitutions <= end {
        BinderRuleCursor::Complete
    } else if end == allowance.binder_search_limit {
        BinderRuleCursor::Exhausted
    } else {
        BinderRuleCursor::Pending { offset: end }
    };

    let matches = matches
        .into_iter()
        .skip(offset)
        .take(end - offset)
        .collect::<Vec<_>>();
    let returned_substitutions = matches.len();
    MatchedRules {
        matches,
        report: RuleSearchReport {
            examined_substitutions,
            returned_substitutions,
            rounds: 1,
            ..Default::default()
        },
    }
}

/// Continue within the SAME model-equivalence graph. A new model must use a
/// new cursor; its e-class identities and matching order may have changed.
#[cfg(test)]
pub(crate) fn search_binder_page<N: egg::Analysis<TermLanguage>>(
    egraph: &egg::EGraph<TermLanguage, N>,
    rules: &[CompiledQuantifiedRule<N>],
    cursor: &mut BinderSearchCursor,
    profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
) -> MatchedRules {
    cursor
        .rules
        .resize(rules.len(), BinderRuleCursor::Pending { offset: 0 });

    let mut result = MatchedRules::default();

    // Find the next pending rule, wrapping around once. For an empty rule
    // list, this iterator is empty and the modulo is never evaluated.
    let next = (0..rules.len())
        .map(|distance| (cursor.next_rule + distance) % rules.len())
        .find(|&index| matches!(cursor.rules[index], BinderRuleCursor::Pending { .. }));

    if let Some(index) = next {
        result = search_binder_rule_page(
            egraph,
            &rules[index],
            index,
            &mut cursor.rules[index],
            &crate::policy::effort::WorkAllowance::default(),
            profiling,
        );

        cursor.next_rule = (index + 1) % rules.len();
    }

    for (index, rule) in rules.iter().enumerate() {
        match cursor.rules[index] {
            BinderRuleCursor::Pending { .. } => {
                result
                    .report
                    .continuable_rules
                    .push(rule.metadata().name().to_owned());
            }
            BinderRuleCursor::Exhausted => {
                result
                    .report
                    .budget_exhausted_rules
                    .push(rule.metadata().name().to_owned());
            }
            BinderRuleCursor::Complete => {}
        }
    }
    result
}

pub(crate) fn search_binder_page_at<N: egg::Analysis<TermLanguage>>(
    egraph: &egg::EGraph<TermLanguage, N>,
    rules: &[CompiledQuantifiedRule<N>],
    cursor: &mut BinderSearchCursor,
    index: usize,
    allowance: &crate::policy::effort::WorkAllowance,
    profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
) -> MatchedRules {
    cursor
        .rules
        .resize(rules.len(), BinderRuleCursor::Pending { offset: 0 });
    let mut result = search_binder_rule_page(
        egraph,
        &rules[index],
        index,
        &mut cursor.rules[index],
        allowance,
        profiling,
    );
    // A cursor records progress; it does not choose the next rule.
    cursor.next_rule = (index + 1) % rules.len();
    for (index, rule) in rules.iter().enumerate() {
        match cursor.rules[index] {
            BinderRuleCursor::Pending { .. } => result
                .report
                .continuable_rules
                .push(rule.metadata().name().to_owned()),
            BinderRuleCursor::Exhausted => result
                .report
                .budget_exhausted_rules
                .push(rule.metadata().name().to_owned()),
            BinderRuleCursor::Complete => {}
        }
    }
    result
}
