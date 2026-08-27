use crate::{
    auxiliary_synthesis::ArrayConflictRecord,
    instantiation_provenance::InstantiationProvenance,
    quantified_rule::{QuantifiedRule, QuantifiedRuleCategory},
    theories::array::{
        array_axioms::{expr_to_term, ArrayExpr},
        candidate_scope::CandidateScope,
    },
    training::{AbstractInstantiationRecord, DecisionRecord},
};

use rustc_hash::FxHashMap;
use smt2parser::concrete::Term;
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    mem,
};

/// One term-selection decision retained beside its complete instantiation.
#[derive(Clone, Debug)]
pub(crate) struct SelectionHistoryDecision {
    pub(crate) decision_key: String,
    pub(crate) chosen_term_hash: String,
}

/// The stable unit over which a selection policy chooses one candidate.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum CandidateGroup {
    MatchRoot(egg::Id),
    Rule,
}

/// One complete quantified-rule candidate and its metadata
#[derive(Clone, Debug)]
pub struct InstantiationCandidate {
    pub rule: QuantifiedRule,
    pub expression: ArrayExpr,
    pub cost: u32,
    pub provenance: InstantiationProvenance,
    pub selected: bool,
    pub decisions: Vec<DecisionRecord>,
    pub(crate) selection_history: Vec<SelectionHistoryDecision>,
    pub abstract_instantiation: Option<AbstractInstantiationRecord>,
    pub conflict: Option<ArrayConflictRecord>,
    pub(crate) group: CandidateGroup,
    /// The candidate was retained only after its formula evaluated to false in
    /// the current model, so batch preparation must not evaluate it again.
    pub(crate) model_violation_verified: bool,
}

#[derive(Debug, Default, Eq, PartialEq)]
pub(crate) struct RuleCandidateCounts {
    pub(crate) generated: usize,
    pub(crate) selected: usize,
}

/// Batch-local outcomes for the strategy's logging and progress checks.
#[derive(Debug, Default)]
pub(crate) struct BatchSummary {
    pub(crate) by_rule: FxHashMap<String, RuleCandidateCounts>,
    pub(crate) rejected_model: usize,
    /// Known, duplicate, or uninstallable candidates.
    pub(crate) rejected_known: usize,
    pub(crate) selected_arrays: usize,
    pub(crate) selected_guards: usize,
    pub(crate) conflicts: usize,
}

impl BatchSummary {
    pub(crate) fn selected_count(&self) -> usize {
        self.selected_arrays + self.selected_guards
    }

    pub(crate) fn record_pruned_model_candidates(&mut self, rule_name: &str, count: usize) {
        self.rejected_model += count;
        self.by_rule
            .entry(rule_name.to_string())
            .or_default()
            .generated += count;
    }
}

/// Candidates generated during one array/guard search pass.
#[derive(Default)]
pub struct InstantiationBatch {
    pub candidates: Vec<InstantiationCandidate>,
}

impl InstantiationBatch {
    pub fn selected(&self) -> impl Iterator<Item = &InstantiationCandidate> {
        self.candidates
            .iter()
            .filter(|candidate| candidate.selected)
    }

    pub fn into_selected(self) -> impl Iterator<Item = InstantiationCandidate> {
        self.candidates
            .into_iter()
            .filter(|candidate| candidate.selected)
    }

    pub(crate) fn extend(&mut self, candidates: impl IntoIterator<Item = InstantiationCandidate>) {
        self.candidates.extend(candidates);
    }

    /// Filter, deduplicate, and select using the supplied problem operations.
    /// `normalize` supplies installable keys; `None` rejects the candidate.
    /// Evaluation errors abort preparation; installed keys are never mutated.
    pub(crate) fn prepare<K>(
        &mut self,
        scope: CandidateScope,
        known: &HashSet<K>,
        evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
        mut normalize: impl FnMut(&InstantiationCandidate) -> Option<K>,
    ) -> anyhow::Result<BatchSummary>
    where
        K: Eq + Hash,
    {
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
        summary.rejected_known = self.select(scope, |candidate| {
            let Some(normalized) = normalize(candidate) else {
                return false;
            };
            !known.contains(&normalized) && seen.insert(normalized)
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
                QuantifiedRuleCategory::Other => {}
            }
            if candidate.conflict.is_some() {
                summary.conflicts += 1;
            }
        }
        Ok(summary)
    }

    fn filter_model(
        &mut self,
        scope: CandidateScope,
        mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
    ) -> anyhow::Result<usize> {
        let before = self.candidates.len();
        let mut eligible = Vec::with_capacity(before);
        let mut evaluations = FxHashMap::<String, String>::default();
        for candidate in mem::take(&mut self.candidates) {
            let requires_model_violation = candidate.rule.category()
                == QuantifiedRuleCategory::TransitionGuard
                || scope.requires_model_violation();
            if !requires_model_violation {
                eligible.push(candidate);
                continue;
            }
            if candidate.model_violation_verified {
                eligible.push(candidate);
                continue;
            }
            let term = expr_to_term(candidate.expression.clone());
            if model_value(&term, &mut evaluate, &mut evaluations)?.trim() == "false" {
                eligible.push(candidate);
            }
        }
        let rejected = before - eligible.len();
        self.candidates = eligible;
        Ok(rejected)
    }

    /// Apply category budgets and return the number rejected by eligibility checks.
    fn select(
        &mut self,
        scope: CandidateScope,
        mut eligible: impl FnMut(&InstantiationCandidate) -> bool,
    ) -> usize {
        for candidate in &mut self.candidates {
            candidate.selected = false;
        }

        // Full search spends its per-e-class budget before novelty checks:
        // rejecting a winner must not promote another match from that group.
        if scope == CandidateScope::AllCandidates {
            self.select_full_axioms();
        }
        let mut rejected = 0;
        self.candidates.retain_mut(|candidate| {
            let full_search_array = scope == CandidateScope::AllCandidates
                && candidate.rule.category() == QuantifiedRuleCategory::ArrayAxiom;
            if full_search_array && !candidate.selected {
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
        self.select_guards();
        if scope == CandidateScope::SourceGroundedOnly {
            self.select_source_axiom();
        }

        for candidate in &mut self.candidates {
            if let Some(record) = &mut candidate.abstract_instantiation {
                record.was_selected = candidate.selected;
            }
            if !candidate.selected
                && (scope == CandidateScope::SourceGroundedOnly
                    || candidate.rule.category() == QuantifiedRuleCategory::TransitionGuard)
            {
                candidate.selection_history.clear();
            }
        }
        rejected
    }

    fn select_guards(&mut self) {
        let mut winners = HashMap::<String, usize>::new();
        for candidate_index in 0..self.candidates.len() {
            let candidate = &self.candidates[candidate_index];
            if candidate.rule.category() != QuantifiedRuleCategory::TransitionGuard {
                continue;
            }

            let winner = winners
                .entry(candidate.rule.name().to_string())
                .or_insert(candidate_index);
            if candidate_precedes(&self.candidates, candidate_index, *winner) {
                *winner = candidate_index;
            }
        }

        for winner in winners.into_values() {
            self.candidates[winner].selected = true;
        }
    }

    fn select_source_axiom(&mut self) {
        let winner = self
            .candidates
            .iter()
            .enumerate()
            .filter(|(_, candidate)| {
                candidate.rule.category() == QuantifiedRuleCategory::ArrayAxiom
            })
            .map(|(index, _)| index)
            .min_by(|left, right| compare_candidates(&self.candidates, *left, *right));

        if let Some(winner) = winner {
            self.candidates[winner].selected = true;
        }
    }

    fn select_full_axioms(&mut self) {
        let mut winners = HashMap::<(String, egg::Id), usize>::new();
        for candidate_index in 0..self.candidates.len() {
            let candidate = &self.candidates[candidate_index];
            if candidate.rule.category() != QuantifiedRuleCategory::ArrayAxiom {
                continue;
            }
            let CandidateGroup::MatchRoot(root) = candidate.group else {
                continue;
            };

            let winner = winners
                .entry((candidate.rule.name().to_string(), root))
                .or_insert(candidate_index);
            if candidate_precedes(&self.candidates, candidate_index, *winner) {
                *winner = candidate_index;
            }
        }

        for winner in winners.into_values() {
            self.candidates[winner].selected = true;
        }
    }
}

pub(crate) fn model_value(
    term: &Term,
    evaluate: &mut impl FnMut(&Term) -> anyhow::Result<String>,
    cache: &mut FxHashMap<String, String>,
) -> anyhow::Result<String> {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return cached_model_value(term, evaluate, cache);
    };
    if qual_identifier.get_name() != "=>" || arguments.len() != 2 {
        return cached_model_value(term, evaluate, cache);
    }

    match cached_model_value(&arguments[0], evaluate, cache)?.trim() {
        "false" => Ok("true".to_string()),
        "true" => cached_model_value(&arguments[1], evaluate, cache),
        _ => cached_model_value(term, evaluate, cache),
    }
}

fn cached_model_value(
    term: &Term,
    evaluate: &mut impl FnMut(&Term) -> anyhow::Result<String>,
    cache: &mut FxHashMap<String, String>,
) -> anyhow::Result<String> {
    let key = term.to_string();
    if let Some(value) = cache.get(&key) {
        return Ok(value.clone());
    }
    let value = evaluate(term)?;
    cache.insert(key, value.clone());
    Ok(value)
}

fn candidate_precedes(
    candidates: &[InstantiationCandidate],
    candidate: usize,
    winner: usize,
) -> bool {
    compare_candidates(candidates, candidate, winner).is_lt()
}

fn compare_candidates(
    candidates: &[InstantiationCandidate],
    left: usize,
    right: usize,
) -> std::cmp::Ordering {
    candidates[left]
        .cost
        .cmp(&candidates[right].cost)
        .then_with(|| {
            candidates[left]
                .expression
                .to_string()
                .cmp(&candidates[right].expression.to_string())
        })
        .then_with(|| left.cmp(&right))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        instantiation_provenance::InstantiationProvenance,
        instantiation_strategy::assertion_tracker::canonical_instantiation_key,
        quantified_rule::{ArrayAxiomKind, QuantifiedRule},
    };
    use smt2parser::vmt::quantified_instantiator::UnquantifiedInstantiator;

    fn array_candidate(expression: ArrayExpr) -> InstantiationCandidate {
        InstantiationCandidate {
            rule: QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, "Int", "Int"),
            expression,
            cost: 0,
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
            candidates: vec![known_winner, alternative, independent],
        };

        let summary = batch
            .prepare(
                CandidateScope::AllCandidates,
                &known,
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
            candidates: vec![winner, loser, independent],
        };

        let summary = batch
            .prepare(
                CandidateScope::AllCandidates,
                &HashSet::new(),
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
                candidates: vec![known_winner, alternative],
            };

            let summary = batch
                .prepare(scope, &known, |_| Ok("false".to_string()), normalized_key)
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
            .parse::<ArrayExpr>()
            .unwrap();
        let expression = "(=> (not (= i@5 i@4)) (= (Read Int Int a@4 i@5) 0))"
            .parse::<ArrayExpr>()
            .unwrap();
        let mut batch = InstantiationBatch {
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
        let installed: ArrayExpr = "(= (Read Int Int a@0 i@0) 0)".parse().unwrap();
        let reversed: ArrayExpr = "(= 0 (Read Int Int a@0 i@0))".parse().unwrap();
        let mut batch = InstantiationBatch {
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
                |_| Ok("false".to_string()),
                normalized_key,
            )
            .unwrap();

        assert_eq!(summary.rejected_known, 1);
        assert!(batch.candidates.is_empty());
    }

    #[test]
    fn only_axioms_false_in_the_current_model_remain_eligible() {
        let satisfied: ArrayExpr = "(= (Read Int Int A i) v)".parse().unwrap();
        let violated: ArrayExpr = "(= (Read Int Int B j) w)".parse().unwrap();
        let mut batch = InstantiationBatch {
            candidates: vec![
                array_candidate(satisfied),
                array_candidate(violated.clone()),
            ],
        };

        let summary = batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
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
        let expression: ArrayExpr = "(= (Read Int Int A i) v)".parse().unwrap();
        let mut guard = array_candidate("(=> guard body)".parse().unwrap());
        guard.rule = QuantifiedRule::transition_guard("guard", 0);
        guard.group = CandidateGroup::Rule;
        let mut source_batch = InstantiationBatch {
            candidates: vec![array_candidate(expression.clone())],
        };
        let mut full_batch = InstantiationBatch {
            candidates: vec![array_candidate(expression.clone()), guard],
        };

        let source_summary = source_batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
                |_| Ok("true".to_string()),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();
        let full_summary = full_batch
            .prepare(
                CandidateScope::AllCandidates,
                &HashSet::new(),
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
        let first: ArrayExpr = "(=> guard (= x y))".parse().unwrap();
        let second: ArrayExpr = "(=> guard (= a b))".parse().unwrap();
        let violated: ArrayExpr = "(= x y)".parse().unwrap();
        let mut batch = InstantiationBatch {
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
                candidates: vec![candidate],
            };

            let error = batch
                .prepare(
                    scope,
                    &HashSet::<String>::new(),
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
            candidates: vec![array_candidate("(= x y)".parse().unwrap())],
        };

        let summary = batch
            .prepare(
                CandidateScope::AllCandidates,
                &HashSet::new(),
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
            candidates: vec![guard],
        };

        let summary = batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
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
        let mut batch = InstantiationBatch { candidates };
        let known = HashSet::from([canonical_instantiation_key(&expr_to_term(
            "(= a b)".parse().unwrap(),
        ))]);
        let mut normalized = Vec::new();

        let summary = batch
            .prepare(
                CandidateScope::SourceGroundedOnly,
                &known,
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
                selected: 1
            }
        );
        assert_eq!(
            summary.by_rule[guard.name()],
            RuleCandidateCounts {
                generated: 2,
                selected: 1
            }
        );
        assert_eq!(
            summary.by_rule[satisfied_guard.name()],
            RuleCandidateCounts {
                generated: 1,
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
}
