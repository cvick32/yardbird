//! Ranking policies for complete array-theory instantiations.
//!
//! Term cost functions decide which representatives are attractive while a
//! rule is grounded. This module is the separate seam for ordering the whole
//! formulas produced by that grounding process.

use std::{cmp::Ordering, fmt::Debug};

use crate::quantified_rule::{ArrayAxiomKind, QuantifiedRuleKind};

use super::{
    candidate_scope::CandidateScope,
    instantiation_candidate::{InstantiationCandidate, InstantiationGrounding},
};

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

    fn source_batch_limit(&self, rule_kind: QuantifiedRuleKind, configured_limit: usize) -> usize {
        if matches!(
            rule_kind,
            QuantifiedRuleKind::ArrayAxiom(ArrayAxiomKind::WriteDoesNotOverwrite)
        ) {
            configured_limit.min(1)
        } else {
            configured_limit
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        instantiation_provenance::InstantiationProvenance,
        quantified_rule::{ArrayAxiomKind, QuantifiedRule},
        theories::array::instantiation_candidate::{CandidateGroup, InstantiationCandidate},
    };

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
