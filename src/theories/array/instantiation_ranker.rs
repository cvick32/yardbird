//! Ranking policies for complete array-theory instantiations.
//!
//! Term cost functions decide which representatives are attractive while a
//! rule is grounded. This module is the separate seam for ordering the whole
//! formulas produced by that grounding process.

use std::{cmp::Ordering, fmt::Debug};

use super::{
    candidate_scope::CandidateScope,
    instantiation_candidate::{InstantiationCandidate, InstantiationGrounding},
};

pub trait InstantiationRanker: Debug + Send {
    fn clone_box(&self) -> Box<dyn InstantiationRanker>;

    fn compare(&self, left: &InstantiationCandidate, right: &InstantiationCandidate) -> Ordering;

    fn is_eligible(&self, _candidate: &InstantiationCandidate, _scope: CandidateScope) -> bool {
        true
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
            .then_with(|| compare_by_term_cost(left, right))
    }

    fn is_eligible(&self, candidate: &InstantiationCandidate, scope: CandidateScope) -> bool {
        scope != CandidateScope::SourceGroundedOnly
            || candidate.grounding == InstantiationGrounding::SourceGrounded
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
}
