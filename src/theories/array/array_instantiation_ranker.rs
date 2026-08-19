//! Programmatic comparison of complete array-axiom instantiations.
//!
//! Term cost functions choose representatives for individual pattern slots.
//! This separate seam compares the complete formulas produced from those
//! choices. The current candidates therefore use preselected slots; a future
//! candidate generator can broaden the candidate set without changing this
//! interface.

use std::{cmp::Ordering, fmt::Debug};

use super::array_axioms::ArrayExpr;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArrayInstantiationCandidate {
    pub expression: ArrayExpr,
    pub complete_cost: u32,
    pub is_const_or_high_cost: bool,
    pub discovery_order: usize,
}

pub trait ArrayInstantiationRanker: Debug + Send {
    fn clone_box(&self) -> Box<dyn ArrayInstantiationRanker>;

    fn compare(
        &self,
        left: &ArrayInstantiationCandidate,
        right: &ArrayInstantiationCandidate,
    ) -> Ordering;

    fn select(&self, candidates: &[ArrayInstantiationCandidate], limit: usize) -> Vec<usize> {
        let mut indices = (0..candidates.len()).collect::<Vec<_>>();
        indices.sort_by(|left, right| self.compare(&candidates[*left], &candidates[*right]));
        indices.truncate(limit.min(indices.len()));
        indices
    }
}

impl Clone for Box<dyn ArrayInstantiationRanker> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

/// Compare complete formulas using the active Yardbird cost function.
#[derive(Clone, Copy, Debug, Default)]
pub struct CompleteCostInstantiationRanker;

impl ArrayInstantiationRanker for CompleteCostInstantiationRanker {
    fn clone_box(&self) -> Box<dyn ArrayInstantiationRanker> {
        Box::new(*self)
    }

    fn compare(
        &self,
        left: &ArrayInstantiationCandidate,
        right: &ArrayInstantiationCandidate,
    ) -> Ordering {
        left.complete_cost
            .cmp(&right.complete_cost)
            .then_with(|| {
                left.expression
                    .to_string()
                    .cmp(&right.expression.to_string())
            })
            .then_with(|| left.discovery_order.cmp(&right.discovery_order))
    }
}

/// Preserve matcher discovery order. This is useful as a control policy and
/// demonstrates that whole-instantiation comparison is independently
/// programmable rather than hard-coded into saturation.
#[derive(Clone, Copy, Debug, Default)]
pub struct DiscoveryOrderInstantiationRanker;

impl ArrayInstantiationRanker for DiscoveryOrderInstantiationRanker {
    fn clone_box(&self) -> Box<dyn ArrayInstantiationRanker> {
        Box::new(*self)
    }

    fn compare(
        &self,
        left: &ArrayInstantiationCandidate,
        right: &ArrayInstantiationCandidate,
    ) -> Ordering {
        left.discovery_order.cmp(&right.discovery_order)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn candidate(
        expression: &str,
        complete_cost: u32,
        discovery_order: usize,
    ) -> ArrayInstantiationCandidate {
        ArrayInstantiationCandidate {
            expression: expression.parse().unwrap(),
            complete_cost,
            is_const_or_high_cost: false,
            discovery_order,
        }
    }

    #[test]
    fn ranking_policy_is_independent_from_candidate_costs() {
        let candidates = vec![candidate("A", 10, 0), candidate("B", 1, 1)];

        assert_eq!(
            CompleteCostInstantiationRanker.select(&candidates, 1),
            vec![1]
        );
        assert_eq!(
            DiscoveryOrderInstantiationRanker.select(&candidates, 1),
            vec![0]
        );
    }
}
