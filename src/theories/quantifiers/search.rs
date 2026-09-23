//! Binder paging and model-local continuation cursors.
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::profiling::RefinementProfilingCollector;

use crate::terms::language::TermLanguage;
use crate::theories::quantifiers::compiled_rule::CompiledBinderRule;

use crate::rule_matching::search::{search, MatchedRules, RuleMatch, RuleSearchReport};
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
    partial: HashMap<usize, super::partial_tuple::PartialTupleCursor>,
}

/// Conflict fallback can test signed conditions on incomplete domain tuples.
/// The cursor, including every pruning decision, belongs to this model/graph.
pub(super) fn search_binder_model_page<N: egg::Analysis<TermLanguage>>(
    egraph: &egg::EGraph<TermLanguage, N>,
    rules: &[CompiledBinderRule<N>],
    cursor: &mut BinderSearchCursor,
    index: Option<usize>,
    allowance: &crate::policy::effort::WorkAllowance,
    profiling: &Option<Rc<RefCell<RefinementProfilingCollector>>>,
    evaluate: impl FnMut(
        &crate::terms::language::TermPattern,
        &egg::Subst,
    ) -> anyhow::Result<Option<bool>>,
) -> anyhow::Result<MatchedRules> {
    cursor
        .rules
        .resize(rules.len(), BinderRuleCursor::Pending { offset: 0 });
    let index = index.or_else(|| {
        (0..rules.len())
            .map(|distance| (cursor.next_rule + distance) % rules.len())
            .find(|&index| matches!(cursor.rules[index], BinderRuleCursor::Pending { .. }))
    });
    let Some(index) = index else {
        let mut result = MatchedRules::default();
        report_progress(rules, cursor, &mut result);
        return Ok(result);
    };
    let rule = &rules[index];
    let Some(plan) = rule
        .details
        .partial
        .as_ref()
        .filter(|_| !rule.is_direct_binder_instance())
    else {
        return Ok(search_binder_page_at(
            egraph, rules, cursor, index, allowance, profiling,
        ));
    };
    let mut result = MatchedRules::default();
    if matches!(cursor.rules[index], BinderRuleCursor::Pending { .. }) {
        let start = std::time::Instant::now();
        let traversal = cursor.partial.entry(index).or_insert_with(|| {
            super::partial_tuple::PartialTupleCursor::new(
                egraph,
                plan,
                allowance.binder_search_limit,
            )
        });
        let page = traversal.page(plan, index, allowance, evaluate)?;
        if let Some(profiling) = profiling {
            let mut profiling = profiling.borrow_mut();
            for (key, count) in [
                (
                    "partial_tuple_prefixes",
                    page.matched.report.examined_substitutions,
                ),
                ("partial_tuple_checks", page.checks),
                ("partial_tuple_rejections", page.rejected),
                ("partial_tuple_survivors", page.matched.matches.len()),
            ] {
                profiling.record_quantifier_counter(rule.metadata().name(), key, count as u64);
            }
            profiling.record_quantifier_timing(
                rule.metadata().name(),
                "partial_tuple_search",
                start.elapsed(),
            );
        }
        cursor.rules[index] = if page.complete {
            BinderRuleCursor::Complete
        } else if page.exhausted {
            BinderRuleCursor::Exhausted
        } else {
            BinderRuleCursor::Pending { offset: 0 }
        };
        result = page.matched;
    }
    cursor.next_rule = (index + 1) % rules.len();
    report_progress(rules, cursor, &mut result);
    Ok(result)
}

fn report_progress<N: egg::Analysis<TermLanguage>>(
    rules: &[CompiledBinderRule<N>],
    cursor: &BinderSearchCursor,
    result: &mut MatchedRules,
) {
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

fn search_binder_rule_page<N: egg::Analysis<TermLanguage>>(
    egraph: &egg::EGraph<TermLanguage, N>,
    rule: &CompiledBinderRule<N>,
    rule_index: usize,
    cursor: &mut BinderRuleCursor,
    allowance: &crate::policy::effort::WorkAllowance,
    profiling: &Option<Rc<RefCell<RefinementProfilingCollector>>>,
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
    if let Some(profiling) = profiling {
        let mut profiling = profiling.borrow_mut();
        if rule.uses_violation_plan() {
            profiling.record_quantifier_counter(
                rule.metadata().name(),
                "violation_plan_searches",
                1,
            );
            profiling.record_quantifier_counter(
                rule.metadata().name(),
                "violation_plan_substitutions_returned",
                examined_substitutions as u64,
            );
        }
    }

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
    rules: &[CompiledBinderRule<N>],
    cursor: &mut BinderSearchCursor,
    profiling: &Option<Rc<RefCell<RefinementProfilingCollector>>>,
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

    report_progress(rules, cursor, &mut result);
    result
}

pub(crate) fn search_binder_page_at<N: egg::Analysis<TermLanguage>>(
    egraph: &egg::EGraph<TermLanguage, N>,
    rules: &[CompiledBinderRule<N>],
    cursor: &mut BinderSearchCursor,
    index: usize,
    allowance: &crate::policy::effort::WorkAllowance,
    profiling: &Option<Rc<RefCell<RefinementProfilingCollector>>>,
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
    report_progress(rules, cursor, &mut result);
    result
}
