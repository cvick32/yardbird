//! Ranking policies for complete quantified-rule instantiations.
//!
//! Term cost functions decide which representatives are attractive while a
//! rule is grounded. This module is the separate seam for ordering the whole
//! formulas produced by that grounding process.

use std::{cmp::Ordering, fmt::Debug};

use crate::rule_matching::rule::QuantifiedRuleKind;

use crate::rule_matching::candidate::{InstantiationCandidate, InstantiationGrounding};
use crate::rule_matching::scope::CandidateScope;

pub trait InstantiationRanker: Debug + Send {
    fn clone_box(&self) -> Box<dyn InstantiationRanker>;

    fn compare(&self, left: &InstantiationCandidate, right: &InstantiationCandidate) -> Ordering;

    fn requires_source_provenance(&self) -> bool {
        false
    }

    fn is_eligible(&self, _candidate: &InstantiationCandidate, _scope: CandidateScope) -> bool {
        true
    }

    /// Pace candidates of one rule kind within a source-grounded batch. The
    /// configured winner budget remains the default for rankers that do not
    /// need a fresh model between particular refinements.
    fn source_batch_limit(&self, _rule_kind: QuantifiedRuleKind, configured_limit: usize) -> usize {
        configured_limit
    }
}

impl Clone for Box<dyn InstantiationRanker> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

fn compare_by_term_cost(left: &InstantiationCandidate, right: &InstantiationCandidate) -> Ordering {
    left.cost.cmp(&right.cost).then_with(|| {
        left.expression
            .to_string()
            .cmp(&right.expression.to_string())
    })
}

/// Preserve the historical whole-candidate ordering supplied by the active
/// term cost function.
#[derive(Clone, Copy, Debug, Default)]
pub struct TermCostInstantiationRanker;

impl InstantiationRanker for TermCostInstantiationRanker {
    fn clone_box(&self) -> Box<dyn InstantiationRanker> {
        Box::new(*self)
    }

    fn compare(&self, left: &InstantiationCandidate, right: &InstantiationCandidate) -> Ordering {
        compare_by_term_cost(left, right)
    }
}

/// Rank a complete source-grounded substitution ahead of any substitution
/// that relies on model-derived representatives, then use term cost.
#[derive(Clone, Copy, Debug, Default)]
pub struct PreferSourceInstantiationRanker;

impl InstantiationRanker for PreferSourceInstantiationRanker {
    fn clone_box(&self) -> Box<dyn InstantiationRanker> {
        Box::new(*self)
    }

    fn compare(&self, left: &InstantiationCandidate, right: &InstantiationCandidate) -> Ordering {
        let left_is_derived = left.grounding == InstantiationGrounding::Derived;
        let right_is_derived = right.grounding == InstantiationGrounding::Derived;
        left_is_derived
            .cmp(&right_is_derived)
            .then_with(|| left.cost.cmp(&right.cost))
            .then_with(|| {
                right
                    .expression
                    .to_string()
                    .cmp(&left.expression.to_string())
            })
    }

    fn requires_source_provenance(&self) -> bool {
        true
    }

    fn is_eligible(&self, candidate: &InstantiationCandidate, scope: CandidateScope) -> bool {
        scope != CandidateScope::SourceGroundedOnly
            || candidate.grounding == InstantiationGrounding::SourceGrounded
    }
}

use crate::rule_matching::{
    candidate::{BatchSummary, CandidateGroup, InstantiationBatch},
    rule::QuantifiedRuleCategory,
};
use smt2parser::concrete::Term;
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

impl InstantiationBatch {
    /// Filter, deduplicate, and select with the baseline term-cost ranker.
    #[cfg(test)]
    pub(crate) fn prepare<K>(
        &mut self,
        scope: CandidateScope,
        known: &HashSet<K>,
        winners_per_group: usize,
        evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
        normalize: impl FnMut(&InstantiationCandidate) -> Option<K>,
    ) -> anyhow::Result<BatchSummary>
    where
        K: Eq + Hash,
    {
        self.prepare_with_ranker(
            scope,
            known,
            winners_per_group,
            &crate::policy::instance_selection::TermCostInstantiationRanker,
            evaluate,
            normalize,
        )
    }

    /// Filter, deduplicate, and select using the supplied problem operations.
    /// `normalize` supplies installable keys; `None` rejects the candidate.
    /// Evaluation errors abort preparation; installed keys are never mutated.
    pub(crate) fn prepare_with_ranker<K>(
        &mut self,
        scope: CandidateScope,
        known: &HashSet<K>,
        winners_per_group: usize,
        ranker: &dyn InstantiationRanker,
        evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
        mut normalize: impl FnMut(&InstantiationCandidate) -> Option<K>,
    ) -> anyhow::Result<BatchSummary>
    where
        K: Eq + Hash,
    {
        assert!(winners_per_group > 0, "candidate groups need a winner");
        let mut summary = BatchSummary::default();
        for candidate in &self.candidates {
            summary
                .by_rule
                .entry(candidate.rule.name().to_string())
                .or_default()
                .generated += 1;
        }

        summary.rejected_model = self.filter_model(scope, evaluate)?;
        let mut seen = HashSet::new();
        (summary.rejected_known, summary.rejected_ranker) =
            self.select(scope, winners_per_group, ranker, |candidate| {
                let accepted = normalize(candidate).is_some_and(|normalized| {
                    !known.contains(&normalized) && seen.insert(normalized)
                });
                if !accepted {
                    summary
                        .by_rule
                        .entry(candidate.rule.name().to_string())
                        .or_default()
                        .rejected_known_or_uninstallable += 1;
                }
                accepted
            });

        for candidate in self.selected() {
            summary
                .by_rule
                .entry(candidate.rule.name().to_string())
                .or_default()
                .selected += 1;
            match candidate.rule.category() {
                QuantifiedRuleCategory::ArrayAxiom => summary.selected_arrays += 1,
                QuantifiedRuleCategory::TransitionGuard => summary.selected_guards += 1,
                QuantifiedRuleCategory::InputBinder => summary.selected_binders += 1,
            }
            if candidate.conflict.is_some() {
                summary.conflicts += 1;
            }
        }
        Ok(summary)
    }

    /// Apply category budgets and return the number rejected by eligibility checks.
    fn select(
        &mut self,
        scope: CandidateScope,
        winners_per_group: usize,
        ranker: &dyn InstantiationRanker,
        mut eligible: impl FnMut(&InstantiationCandidate) -> bool,
    ) -> (usize, usize) {
        for candidate in &mut self.candidates {
            candidate.selected = false;
        }

        // Full search spends its per-e-class budget before novelty checks:
        // rejecting a winner must not promote another match from that group.
        if scope == CandidateScope::AllCandidates {
            self.select_groups(winners_per_group, ranker, |candidate| {
                candidate.rule.category() == QuantifiedRuleCategory::ArrayAxiom
                    && matches!(candidate.group, CandidateGroup::MatchRoot(_))
            });
        }
        let mut rejected = 0;
        let mut rejected_ranker = 0;
        self.candidates.retain_mut(|candidate| {
            let full_search_array = scope == CandidateScope::AllCandidates
                && candidate.rule.category() == QuantifiedRuleCategory::ArrayAxiom;
            if full_search_array && !candidate.selected {
                candidate.selection_history.clear();
                return true;
            }
            if !ranker.is_eligible(candidate, scope) {
                rejected_ranker += 1;
                candidate.selected = false;
                candidate.selection_history.clear();
                return true;
            }
            if eligible(candidate) {
                return true;
            }

            rejected += 1;
            candidate.selected = false;
            // Full-search attempts retain extraction history for later rounds,
            // even when the chosen instantiation is already installed.
            full_search_array
        });

        // Guards and source-grounded axioms choose from eligible candidates.
        self.select_guards(scope, ranker);
        self.select_groups(winners_per_group, ranker, |candidate| {
            candidate.rule.category() == QuantifiedRuleCategory::InputBinder
                && ranker.is_eligible(candidate, scope)
        });
        if scope == CandidateScope::SourceGroundedOnly {
            self.select_source_axioms(winners_per_group, ranker);
            self.order_source_installations(ranker);
        }

        for candidate in &mut self.candidates {
            if let Some(record) = &mut candidate.abstract_instantiation {
                record.was_selected = candidate.selected;
            }
            if !candidate.selected
                && (scope == CandidateScope::SourceGroundedOnly
                    || candidate.rule.category() != QuantifiedRuleCategory::ArrayAxiom)
            {
                candidate.selection_history.clear();
            }
        }
        (rejected, rejected_ranker)
    }

    fn select_guards(&mut self, scope: CandidateScope, ranker: &dyn InstantiationRanker) {
        let mut winners = HashMap::<String, usize>::new();
        for candidate_index in 0..self.candidates.len() {
            let candidate = &self.candidates[candidate_index];
            if candidate.rule.category() != QuantifiedRuleCategory::TransitionGuard {
                continue;
            }
            if !ranker.is_eligible(candidate, scope) {
                continue;
            }

            let winner = winners
                .entry(candidate.rule.name().to_string())
                .or_insert(candidate_index);
            if candidate_precedes(ranker, &self.candidates, candidate_index, *winner) {
                *winner = candidate_index;
            }
        }

        for winner in winners.into_values() {
            self.candidates[winner].selected = true;
        }
    }

    fn select_source_axioms(&mut self, winners_per_group: usize, ranker: &dyn InstantiationRanker) {
        let mut winners = self
            .candidates
            .iter()
            .enumerate()
            .filter(|(_, candidate)| {
                candidate.rule.category() == QuantifiedRuleCategory::ArrayAxiom
                    && ranker.is_eligible(candidate, CandidateScope::SourceGroundedOnly)
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        winners.sort_by(|left, right| compare_candidates(ranker, &self.candidates, *left, *right));

        let mut selected = 0;
        let mut selected_by_rule = HashMap::<QuantifiedRuleKind, usize>::new();
        for winner in winners {
            if selected == winners_per_group {
                break;
            }
            let rule_kind = self.candidates[winner].rule.kind();
            let rule_limit = ranker.source_batch_limit(rule_kind, winners_per_group);
            let selected_for_rule = selected_by_rule.entry(rule_kind).or_default();
            if *selected_for_rule >= rule_limit {
                continue;
            }

            self.candidates[winner].selected = true;
            selected += 1;
            *selected_for_rule += 1;
        }
    }

    /// Make the configured whole-instantiation ranker control array assertion
    /// order, not just which source-grounded candidates survive the batch
    /// budget. Other rule categories retain generation order.
    fn order_source_installations(&mut self, ranker: &dyn InstantiationRanker) {
        let positions = self
            .candidates
            .iter()
            .enumerate()
            .filter(|(_, candidate)| {
                candidate.selected
                    && candidate.rule.category() == QuantifiedRuleCategory::ArrayAxiom
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let mut ordered = positions
            .iter()
            .map(|index| self.candidates[*index].clone())
            .collect::<Vec<_>>();
        ordered.sort_by(|left, right| ranker.compare(left, right));
        for (index, candidate) in positions.into_iter().zip(ordered) {
            self.candidates[index] = candidate;
        }
    }

    /// The same group ranking applies to model-equality matches and input
    /// binders. Scheduling decides when novelty is checked, not how to rank.
    fn select_groups(
        &mut self,
        winners_per_group: usize,
        ranker: &dyn InstantiationRanker,
        eligible: impl Fn(&InstantiationCandidate) -> bool,
    ) {
        let mut groups = HashMap::<(String, CandidateGroup), Vec<usize>>::new();
        for (index, candidate) in self.candidates.iter().enumerate() {
            if eligible(candidate) {
                groups
                    .entry((candidate.rule.name().to_string(), candidate.group))
                    .or_default()
                    .push(index);
            }
        }
        for mut group in groups.into_values() {
            group
                .sort_by(|left, right| compare_candidates(ranker, &self.candidates, *left, *right));
            for winner in group.into_iter().take(winners_per_group) {
                self.candidates[winner].selected = true;
            }
        }
    }
}

fn candidate_precedes(
    ranker: &dyn InstantiationRanker,
    candidates: &[InstantiationCandidate],
    candidate: usize,
    winner: usize,
) -> bool {
    compare_candidates(ranker, candidates, candidate, winner).is_lt()
}

fn compare_candidates(
    ranker: &dyn InstantiationRanker,
    candidates: &[InstantiationCandidate],
    left: usize,
    right: usize,
) -> std::cmp::Ordering {
    ranker
        .compare(&candidates[left], &candidates[right])
        .then_with(|| left.cmp(&right))
}

#[cfg(test)]
mod ranker_tests {
    use super::*;
    use crate::rule_matching::candidate::{CandidateGroup, InstantiationCandidate};
    use crate::rule_matching::provenance::InstantiationProvenance;
    use crate::rule_matching::rule::QuantifiedRule;
    use crate::theories::array::rule::ArrayAxiomKind;

    fn candidate(
        expression: &str,
        cost: u32,
        grounding: InstantiationGrounding,
    ) -> InstantiationCandidate {
        InstantiationCandidate {
            rule: QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, "Int", "Int"),
            expression: expression.parse().unwrap(),
            cost,
            grounding,
            provenance: InstantiationProvenance::new("test".to_string(), vec![]),
            selected: false,
            decisions: vec![],
            selection_history: vec![],
            abstract_instantiation: None,
            conflict: None,
            group: CandidateGroup::MatchRoot(egg::Id::from(0)),
            model_violation_verified: false,
        }
    }

    #[test]
    fn term_cost_ranker_can_prefer_a_cheaper_derived_instantiation() {
        let source = candidate("(= source 0)", 10, InstantiationGrounding::SourceGrounded);
        let derived = candidate("(= derived 0)", 1, InstantiationGrounding::Derived);

        assert!(TermCostInstantiationRanker
            .compare(&derived, &source)
            .is_lt());
    }

    #[test]
    fn source_ranker_prefers_the_whole_source_grounded_instantiation() {
        let source = candidate("(= source 0)", 10, InstantiationGrounding::SourceGrounded);
        let derived = candidate("(= derived 0)", 1, InstantiationGrounding::Derived);

        assert!(PreferSourceInstantiationRanker
            .compare(&source, &derived)
            .is_lt());
    }

    #[test]
    fn source_ranker_reverses_equal_cost_canonical_ties() {
        let first = candidate(
            "conditional_first",
            3,
            InstantiationGrounding::SourceGrounded,
        );
        let second = candidate(
            "conditional_second",
            3,
            InstantiationGrounding::SourceGrounded,
        );

        assert!(PreferSourceInstantiationRanker
            .compare(&second, &first)
            .is_lt());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instance_installation::assertion_tracker::canonical_instantiation_key;
    use crate::policy::instance_selection::{
        PreferSourceInstantiationRanker, TermCostInstantiationRanker,
    };
    use crate::rule_matching::provenance::InstantiationProvenance;
    use crate::rule_matching::rule::QuantifiedRule;
    use crate::theories::array::rule::ArrayAxiomKind;
    use crate::{
        auxiliary_synthesis::ArrayConflictRecord,
        rule_matching::candidate::{RuleCandidateCounts, SelectionHistoryDecision},
        terms::language::{expr_to_term, TermExpr},
        training::AbstractInstantiationRecord,
    };
    use smt2parser::vmt::quantified_instantiator::UnquantifiedInstantiator;

    fn array_candidate(expression: TermExpr) -> InstantiationCandidate {
        InstantiationCandidate {
            rule: QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, "Int", "Int"),
            expression,
            cost: 0,
            grounding: InstantiationGrounding::SourceGrounded,
            provenance: InstantiationProvenance::new("test".to_string(), vec![]),
            selected: false,
            decisions: vec![],
            selection_history: vec![],
            abstract_instantiation: None,
            conflict: None,
            group: CandidateGroup::MatchRoot(egg::Id::from(0)),
            model_violation_verified: false,
        }
    }

    fn normalized_key(candidate: &InstantiationCandidate) -> Option<Term> {
        UnquantifiedInstantiator::rewrite_unquantified(
            expr_to_term(candidate.expression.clone()),
            vec![],
        )
        .map(|instance| canonical_instantiation_key(instance.get_term()))
    }

    #[test]
    fn batch_selection_uses_the_configured_whole_instantiation_ranker() {
        let mut source = array_candidate("(= source 0)".parse().unwrap());
        source.cost = 10;
        let mut derived = array_candidate("(= derived 0)".parse().unwrap());
        derived.cost = 1;
        derived.grounding = InstantiationGrounding::Derived;
        let expected = source.expression.clone();
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![derived, source],
        };

        batch
            .prepare_with_ranker(
                CandidateScope::AllCandidates,
                &HashSet::<Term>::new(),
                1,
                &PreferSourceInstantiationRanker,
                |_| Ok("false".to_string()),
                |candidate| Some(expr_to_term(candidate.expression.clone())),
            )
            .unwrap();

        assert_eq!(
            batch
                .selected()
                .map(|candidate| &candidate.expression)
                .collect::<Vec<_>>(),
            vec![&expected]
        );
    }

    #[test]
    fn full_search_skips_known_group() {
        let installed = array_candidate("(= (Read Int Int a@0 i@0) 0)".parse().unwrap());
        let mut known_winner = array_candidate("(= (Read Int Int a@2 i@2) 0)".parse().unwrap());
        known_winner
            .selection_history
            .push(SelectionHistoryDecision {
                decision_key: "known-winner".to_string(),
                chosen_term_hash: "winner-term".to_string(),
            });
        let mut alternative = array_candidate("(= (Read Int Int a@2 i@2) 1)".parse().unwrap());
        alternative.cost = 1;
        alternative
            .selection_history
            .push(SelectionHistoryDecision {
                decision_key: "alternative".to_string(),
                chosen_term_hash: "alternative-term".to_string(),
            });
        let mut independent = array_candidate("(= (Read Int Int b@2 j@2) 0)".parse().unwrap());
        independent.group = CandidateGroup::MatchRoot(egg::Id::from(1));
        let expected = independent.expression.clone();
        let known = HashSet::from([normalized_key(&installed).unwrap()]);
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![known_winner, alternative, independent],
        };

        let summary = batch
            .prepare(
                CandidateScope::AllCandidates,
                &known,
                1,
                |_| Ok("false".to_string()),
                normalized_key,
            )
            .unwrap();

        assert_eq!(summary.rejected_known, 1);
        assert_eq!(
            batch.selected().map(|c| &c.expression).collect::<Vec<_>>(),
            vec![&expected],
        );
        assert_eq!(known.len(), 1);
        assert_eq!(
            batch
                .candidates
                .iter()
                .flat_map(|c| &c.selection_history)
                .map(|decision| decision.chosen_term_hash.as_str())
                .collect::<Vec<_>>(),
            vec!["winner-term"],
        );
    }

    #[test]
    fn full_losers_do_not_deduplicate() {
        let winner = array_candidate("(= (Read Int Int a@2 i@2) 0)".parse().unwrap());
        let mut loser = array_candidate("(= (Read Int Int b@2 j@2) 0)".parse().unwrap());
        loser.cost = 1;
        let mut independent = array_candidate("(= (Read Int Int b@4 j@4) 0)".parse().unwrap());
        independent.group = CandidateGroup::MatchRoot(egg::Id::from(1));
        let expected = vec![winner.expression.clone(), independent.expression.clone()];
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![winner, loser, independent],
        };

        let summary = batch
            .prepare(
                CandidateScope::AllCandidates,
                &HashSet::new(),
                1,
                |_| Ok("false".to_string()),
                normalized_key,
            )
            .unwrap();

        assert_eq!(summary.rejected_known, 0);
        assert_eq!(
            batch
                .selected()
                .map(|c| c.expression.clone())
                .collect::<Vec<_>>(),
            expected,
        );
    }

    #[test]
    fn other_policies_skip_known() {
        for (scope, rule) in [
            (
                CandidateScope::SourceGroundedOnly,
                QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, "Int", "Int"),
            ),
            (
                CandidateScope::SourceGroundedOnly,
                QuantifiedRule::transition_guard("guard", 0),
            ),
            (
                CandidateScope::AllCandidates,
                QuantifiedRule::transition_guard("guard", 0),
            ),
        ] {
            let mut known_winner = array_candidate("(= (Read Int Int a@2 i@2) 0)".parse().unwrap());
            if rule.category() == QuantifiedRuleCategory::TransitionGuard {
                known_winner.group = CandidateGroup::Rule;
            }
            known_winner.rule = rule.clone();
            let mut alternative = array_candidate("(= (Read Int Int a@2 i@2) 1)".parse().unwrap());
            alternative.group = known_winner.group;
            alternative.rule = rule;
            alternative.cost = 1;
            let expected = alternative.expression.clone();
            let known = HashSet::from([normalized_key(&known_winner).unwrap()]);
            let mut batch = InstantiationBatch {
                search: Default::default(),
                candidates: vec![known_winner, alternative],
            };

            let summary = batch
                .prepare(
                    scope,
                    &known,
                    1,
                    |_| Ok("false".to_string()),
                    normalized_key,
                )
                .unwrap();

            assert_eq!(summary.rejected_known, 1);
            assert_eq!(
                batch.selected().map(|c| &c.expression).collect::<Vec<_>>(),
                vec![&expected],
            );
        }
    }

    #[test]
    fn shifted_copies_of_an_instantiation_are_duplicate_after_normalization() {
        let installed = "(=> (not (= i@12 i@11)) (= (Read Int Int a@11 i@12) 0))"
            .parse::<TermExpr>()
            .unwrap();
        let expression = "(=> (not (= i@5 i@4)) (= (Read Int Int a@4 i@5) 0))"
            .parse::<TermExpr>()
            .unwrap();
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![array_candidate(expression)],
        };
        let known = HashSet::from([UnquantifiedInstantiator::rewrite_unquantified(
            expr_to_term(installed),
            vec![],
        )
        .unwrap()
        .get_term()
        .clone()]);

        let summary = batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &known,
                1,
                |term| Ok(term.to_string().starts_with("(not ").to_string()),
                |candidate| {
                    UnquantifiedInstantiator::rewrite_unquantified(
                        expr_to_term(candidate.expression.clone()),
                        vec![],
                    )
                    .map(|instance| instance.get_term().clone())
                },
            )
            .unwrap();

        assert_eq!(summary.rejected_known, 1);
        assert!(batch.candidates.is_empty());
        assert_eq!(known.len(), 1);
    }

    #[test]
    fn reversed_equalities_are_duplicate_before_whole_candidate_selection() {
        let installed: TermExpr = "(= (Read Int Int a@0 i@0) 0)".parse().unwrap();
        let reversed: TermExpr = "(= 0 (Read Int Int a@0 i@0))".parse().unwrap();
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![array_candidate(reversed)],
        };
        let installed =
            UnquantifiedInstantiator::rewrite_unquantified(expr_to_term(installed), vec![])
                .unwrap();
        let known = HashSet::from([canonical_instantiation_key(installed.get_term())]);

        let summary = batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &known,
                1,
                |_| Ok("false".to_string()),
                normalized_key,
            )
            .unwrap();

        assert_eq!(summary.rejected_known, 1);
        assert!(batch.candidates.is_empty());
    }

    #[test]
    fn only_axioms_false_in_the_current_model_remain_eligible() {
        let satisfied: TermExpr = "(= (Read Int Int A i) v)".parse().unwrap();
        let violated: TermExpr = "(= (Read Int Int B j) w)".parse().unwrap();
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![
                array_candidate(satisfied),
                array_candidate(violated.clone()),
            ],
        };

        let summary = batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
                1,
                |term| {
                    Ok(if term.to_string().contains("Read_Int_Int A") {
                        "true".to_string()
                    } else {
                        "false".to_string()
                    })
                },
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();

        assert_eq!(summary.rejected_model, 1);
        assert_eq!(batch.candidates.len(), 1);
        assert_eq!(batch.candidates[0].expression, violated);
    }

    #[test]
    fn full_search_keeps_egraph_conflicts_even_when_the_formula_is_model_satisfied() {
        let expression: TermExpr = "(= (Read Int Int A i) v)".parse().unwrap();
        let mut guard = array_candidate("(=> guard body)".parse().unwrap());
        guard.rule = QuantifiedRule::transition_guard("guard", 0);
        guard.group = CandidateGroup::Rule;
        let mut source_batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![array_candidate(expression.clone())],
        };
        let mut full_batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![array_candidate(expression.clone()), guard],
        };

        let source_summary = source_batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
                1,
                |_| Ok("true".to_string()),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();
        let full_summary = full_batch
            .prepare(
                CandidateScope::AllCandidates,
                &HashSet::new(),
                1,
                |_| Ok("true".to_string()),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();

        assert_eq!(source_summary.rejected_model, 1);
        assert!(source_batch.candidates.is_empty());
        assert_eq!(full_summary.rejected_model, 1);
        assert_eq!(full_batch.candidates.len(), 1);
        assert_eq!(full_batch.candidates[0].expression, expression);
    }

    #[test]
    fn model_filter_reuses_implication_guards() {
        let first: TermExpr = "(=> guard (= x y))".parse().unwrap();
        let second: TermExpr = "(=> guard (= a b))".parse().unwrap();
        let violated: TermExpr = "(= x y)".parse().unwrap();
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![
                array_candidate(first),
                array_candidate(second),
                array_candidate(violated.clone()),
            ],
        };
        let mut evaluated = Vec::new();

        let summary = batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
                1,
                |term| {
                    evaluated.push(term.to_string());
                    Ok("false".to_string())
                },
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();

        assert_eq!(summary.rejected_model, 2);
        assert_eq!(batch.candidates.len(), 1);
        assert_eq!(batch.candidates[0].expression, violated);
        assert_eq!(evaluated, vec!["guard", "(= x y)"]);
    }

    #[test]
    fn evaluation_errors_abort_batch() {
        let array = QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, "Int", "Int");
        let guard = QuantifiedRule::transition_guard("guard", 0);
        for (scope, rule) in [
            (CandidateScope::SourceGroundedOnly, array),
            (CandidateScope::SourceGroundedOnly, guard.clone()),
            (CandidateScope::AllCandidates, guard),
        ] {
            let mut candidate = array_candidate("(= x y)".parse().unwrap());
            candidate.rule = rule;
            let mut batch = InstantiationBatch {
                search: Default::default(),
                candidates: vec![candidate],
            };

            let error = batch
                .prepare(
                    scope,
                    &HashSet::<String>::new(),
                    1,
                    |_| Err(anyhow::anyhow!("model evaluation failed")),
                    |_| panic!("eligibility must not run after an evaluation error"),
                )
                .unwrap_err();

            assert_eq!(error.to_string(), "model evaluation failed");
        }
    }

    #[test]
    fn full_search_skips_model_eval() {
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![array_candidate("(= x y)".parse().unwrap())],
        };

        let summary = batch
            .prepare(
                CandidateScope::AllCandidates,
                &HashSet::new(),
                1,
                |_| panic!("full-search array violations are checked in the e-graph"),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();

        assert_eq!(summary.rejected_model, 0);
        assert_eq!(summary.selected_count(), 1);
    }

    #[test]
    fn verified_guard_violation_skips_model_re_evaluation() {
        let mut guard = array_candidate("(= x y)".parse().unwrap());
        guard.rule = QuantifiedRule::transition_guard("guard", 0);
        guard.group = CandidateGroup::Rule;
        guard.model_violation_verified = true;
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![guard],
        };

        let summary = batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
                1,
                |_| panic!("a lazily materialized guard was already model-checked"),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();

        assert_eq!(summary.rejected_model, 0);
        assert_eq!(summary.selected_guards, 1);
    }

    #[test]
    fn preparation_reports_outcomes() {
        let array = QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, "Int", "Int");
        let guard = QuantifiedRule::transition_guard("guard", 0);
        let satisfied_guard = QuantifiedRule::transition_guard("satisfied", 0);
        let mut candidates = [
            "(= a a)", "(= a b)", "(= a c)", "(= b c)", "(= c b)", "(= c d)",
        ]
        .into_iter()
        .enumerate()
        .map(|(cost, expression)| {
            candidate(
                array.clone(),
                expression,
                cost as u32,
                CandidateGroup::MatchRoot(egg::Id::from(0)),
            )
        })
        .collect::<Vec<_>>();
        candidates.extend([
            candidate(guard.clone(), "(= p q)", 0, CandidateGroup::Rule),
            candidate(guard.clone(), "(= p r)", 1, CandidateGroup::Rule),
            candidate(satisfied_guard.clone(), "(= s s)", 0, CandidateGroup::Rule),
        ]);
        for (ordinal, candidate) in candidates.iter_mut().enumerate() {
            let expression = candidate.expression.to_string();
            candidate.selection_history.push(SelectionHistoryDecision {
                decision_key: expression.clone(),
                chosen_term_hash: expression.clone(),
            });
            candidate.abstract_instantiation = Some(AbstractInstantiationRecord {
                abstract_instantiation_id: expression.clone(),
                term: expression.clone(),
                term_hash: expression.clone(),
                axiom_name: candidate.rule.name().to_string(),
                bmc_depth: 0,
                refinement_step: 0,
                decision_keys: vec![expression.clone()],
                substitution: vec![],
                was_selected: true,
                indexed_assertions_attempted: 0,
                indexed_assertions_added: 0,
                indexed_assertions_deduplicated: 0,
                helper_assertions_attempted: 0,
                helper_assertions_added: 0,
                helper_assertions_deduplicated: 0,
                in_unsat_core: false,
            });
            candidate.conflict = Some(ArrayConflictRecord::new(
                ordinal,
                expression,
                candidate.rule.name(),
                candidate.expression.clone(),
                expr_to_term(candidate.expression.clone()),
                0,
                0,
                candidate.cost,
                vec![],
            ));
        }
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates,
        };
        let known = HashSet::from([canonical_instantiation_key(&expr_to_term(
            "(= a b)".parse().unwrap(),
        ))]);
        let mut normalized = Vec::new();

        let summary = batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &known,
                1,
                |term| Ok(matches!(term.to_string().as_str(), "(= a a)" | "(= s s)").to_string()),
                |candidate| {
                    let expression = candidate.expression.to_string();
                    normalized.push(expression.clone());
                    if expression == "(= a c)" {
                        return None;
                    }
                    Some(canonical_instantiation_key(&expr_to_term(
                        candidate.expression.clone(),
                    )))
                },
            )
            .unwrap();

        assert_eq!(summary.rejected_model, 2);
        assert_eq!(summary.rejected_known, 3);
        assert_eq!(summary.selected_arrays, 1);
        assert_eq!(summary.selected_guards, 1);
        assert_eq!(summary.selected_count(), 2);
        assert_eq!(summary.conflicts, 2);
        assert_eq!(
            summary.by_rule[array.name()],
            RuleCandidateCounts {
                generated: 6,
                rejected_known_or_uninstallable: 3,
                selected: 1
            }
        );
        assert_eq!(
            summary.by_rule[guard.name()],
            RuleCandidateCounts {
                generated: 2,
                rejected_known_or_uninstallable: 0,
                selected: 1
            }
        );
        assert_eq!(
            summary.by_rule[satisfied_guard.name()],
            RuleCandidateCounts {
                generated: 1,
                rejected_known_or_uninstallable: 0,
                selected: 0
            }
        );
        assert_eq!(known.len(), 1);
        assert_eq!(
            normalized,
            vec!["(= a b)", "(= a c)", "(= b c)", "(= c b)", "(= c d)", "(= p q)", "(= p r)"]
        );
        assert_eq!(
            batch
                .selected()
                .map(|candidate| candidate.expression.to_string())
                .collect::<Vec<_>>(),
            vec!["(= b c)", "(= p q)"],
        );
        for candidate in &batch.candidates {
            assert_eq!(
                candidate
                    .abstract_instantiation
                    .as_ref()
                    .unwrap()
                    .was_selected,
                candidate.selected
            );
            assert_eq!(
                candidate.selection_history.len(),
                usize::from(candidate.selected)
            );
        }
    }

    fn candidate(
        rule: QuantifiedRule,
        expression: &str,
        cost: u32,
        group: CandidateGroup,
    ) -> InstantiationCandidate {
        InstantiationCandidate {
            rule,
            expression: expression.parse().unwrap(),
            cost,
            grounding: InstantiationGrounding::SourceGrounded,
            provenance: InstantiationProvenance::new(expression.to_string(), vec![]),
            selected: false,
            decisions: vec![],
            selection_history: vec![],
            abstract_instantiation: None,
            conflict: None,
            group,
            model_violation_verified: false,
        }
    }

    #[test]
    fn selection_keeps_one_candidate_per_guard_rule() {
        let first_guard = QuantifiedRule::transition_guard("first", 0);
        let second_guard = QuantifiedRule::transition_guard("second", 0);
        let array_rule = QuantifiedRule::array_axiom(ArrayAxiomKind::ReadAfterWrite, "Int", "Int");
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![
                candidate(
                    first_guard.clone(),
                    "first_expensive",
                    10,
                    CandidateGroup::Rule,
                ),
                candidate(first_guard, "first_cheap", 1, CandidateGroup::Rule),
                candidate(second_guard, "second", 2, CandidateGroup::Rule),
                candidate(
                    array_rule,
                    "array",
                    0,
                    CandidateGroup::MatchRoot(egg::Id::from(0)),
                ),
            ],
        };

        batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
                1,
                |_| Ok("false".to_string()),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();

        let selected = batch
            .selected()
            .map(|candidate| candidate.expression.to_string())
            .collect::<Vec<_>>();
        assert_eq!(selected, vec!["first_cheap", "second", "array"]);
    }

    #[test]
    fn source_selection_keeps_the_configured_number_of_array_winners() {
        let array_rule = QuantifiedRule::array_axiom(ArrayAxiomKind::ReadAfterWrite, "Int", "Int");
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![
                candidate(
                    array_rule.clone(),
                    "expensive",
                    10,
                    CandidateGroup::MatchRoot(egg::Id::from(0)),
                ),
                candidate(
                    array_rule.clone(),
                    "cheapest",
                    1,
                    CandidateGroup::MatchRoot(egg::Id::from(1)),
                ),
                candidate(
                    array_rule,
                    "middle",
                    5,
                    CandidateGroup::MatchRoot(egg::Id::from(2)),
                ),
            ],
        };

        batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
                2,
                |_| Ok("false".to_string()),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();

        assert_eq!(
            batch
                .selected()
                .map(|candidate| candidate.expression.to_string())
                .collect::<Vec<_>>(),
            vec!["cheapest", "middle"]
        );
    }

    #[test]
    fn source_selection_honors_budget_for_conditional_array_winners() {
        let unconditional =
            QuantifiedRule::array_axiom(ArrayAxiomKind::ReadAfterWrite, "Int", "Int");
        let conditional =
            QuantifiedRule::array_axiom(ArrayAxiomKind::WriteDoesNotOverwrite, "Int", "Int");
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![
                candidate(
                    unconditional.clone(),
                    "unconditional_one",
                    1,
                    CandidateGroup::MatchRoot(egg::Id::from(0)),
                ),
                candidate(
                    unconditional,
                    "unconditional_two",
                    2,
                    CandidateGroup::MatchRoot(egg::Id::from(1)),
                ),
                candidate(
                    conditional.clone(),
                    "conditional_first",
                    3,
                    CandidateGroup::MatchRoot(egg::Id::from(2)),
                ),
                candidate(
                    conditional,
                    "conditional_second",
                    3,
                    CandidateGroup::MatchRoot(egg::Id::from(3)),
                ),
            ],
        };

        batch
            .prepare_with_ranker(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
                16,
                &PreferSourceInstantiationRanker,
                |_| Ok("false".to_string()),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();

        assert_eq!(
            batch
                .selected()
                .map(|candidate| candidate.expression.to_string())
                .collect::<Vec<_>>(),
            vec![
                "unconditional_one",
                "unconditional_two",
                "conditional_second",
                "conditional_first",
            ]
        );
    }

    #[test]
    fn source_preservation_batch_size_follows_configured_budget() {
        let rule = QuantifiedRule::array_axiom(ArrayAxiomKind::WriteDoesNotOverwrite, "Int", "Int");
        for budget in [1, 4, 16, 32] {
            let mut batch = InstantiationBatch {
                search: Default::default(),
                candidates: (0..20)
                    .map(|index| {
                        candidate(
                            rule.clone(),
                            &format!("preservation_{index}"),
                            index as u32,
                            CandidateGroup::MatchRoot(egg::Id::from(index)),
                        )
                    })
                    .collect(),
            };
            batch
                .prepare_with_ranker(
                    CandidateScope::SourceGroundedOnly,
                    &HashSet::new(),
                    budget,
                    &PreferSourceInstantiationRanker,
                    |_| Ok("false".to_string()),
                    |candidate| Some(candidate.expression.clone()),
                )
                .unwrap();
            assert_eq!(batch.selected().count(), budget.min(20), "budget {budget}");
        }
    }

    #[test]
    fn term_cost_ranker_keeps_configured_conditional_batch_size() {
        let conditional =
            QuantifiedRule::array_axiom(ArrayAxiomKind::WriteDoesNotOverwrite, "Int", "Int");
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![
                candidate(
                    conditional.clone(),
                    "conditional_first",
                    1,
                    CandidateGroup::MatchRoot(egg::Id::from(0)),
                ),
                candidate(
                    conditional,
                    "conditional_second",
                    2,
                    CandidateGroup::MatchRoot(egg::Id::from(1)),
                ),
            ],
        };

        batch
            .prepare_with_ranker(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
                2,
                &TermCostInstantiationRanker,
                |_| Ok("false".to_string()),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();

        assert_eq!(batch.selected().count(), 2);
    }

    #[test]
    fn full_selection_keeps_the_configured_number_of_winners_per_rule_and_root() {
        let array_rule = QuantifiedRule::array_axiom(ArrayAxiomKind::ReadAfterWrite, "Int", "Int");
        let mut batch = InstantiationBatch {
            search: Default::default(),
            candidates: vec![
                candidate(
                    array_rule.clone(),
                    "root_zero_expensive",
                    10,
                    CandidateGroup::MatchRoot(egg::Id::from(0)),
                ),
                candidate(
                    array_rule.clone(),
                    "root_zero_cheapest",
                    1,
                    CandidateGroup::MatchRoot(egg::Id::from(0)),
                ),
                candidate(
                    array_rule.clone(),
                    "root_zero_middle",
                    5,
                    CandidateGroup::MatchRoot(egg::Id::from(0)),
                ),
                candidate(
                    array_rule.clone(),
                    "root_one_expensive",
                    8,
                    CandidateGroup::MatchRoot(egg::Id::from(1)),
                ),
                candidate(
                    array_rule,
                    "root_one_cheapest",
                    2,
                    CandidateGroup::MatchRoot(egg::Id::from(1)),
                ),
            ],
        };

        batch
            .prepare(
                CandidateScope::AllCandidates,
                &HashSet::new(),
                2,
                |_| panic!("full-search array conflicts do not require model evaluation"),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();

        assert_eq!(
            batch
                .selected()
                .map(|candidate| candidate.expression.to_string())
                .collect::<Vec<_>>(),
            vec![
                "root_zero_cheapest",
                "root_zero_middle",
                "root_one_expensive",
                "root_one_cheapest",
            ]
        );
    }
}
