//! Eligibility policy for terms considered during array-axiom matching.
//!
//! Candidate scope answers which representatives may participate and how far
//! matching must search. It deliberately does not score terms or complete
//! instantiations; those decisions belong to the configured cost function and
//! instantiation ranker, respectively.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateScope {
    SourceGroundedOnly,
    SourceThenDerived,
    AllCandidates,
}

impl CandidateScope {
    pub fn requires_source_grounded(self) -> bool {
        self == Self::SourceGroundedOnly
    }

    pub fn allows_derived(self) -> bool {
        !self.requires_source_grounded()
    }

    /// The staged widened scope explicitly combines source and model-derived
    /// catalogs. Legacy full matching keeps its historical cost-function
    /// vocabulary so existing cost functions are not silently specialized.
    pub fn combines_provenance_catalogs(self) -> bool {
        self == Self::SourceThenDerived
    }

    pub fn tracks_provenance(self) -> bool {
        self != Self::AllCandidates
    }

    /// Source provenance is a deterministic tie-breaker, never a substitute
    /// for the configured term cost.
    pub fn prefers_source_on_cost_tie(self) -> bool {
        self != Self::AllCandidates
    }

    pub fn requires_model_violation(self) -> bool {
        self != Self::AllCandidates
    }

    pub fn retries_rejected_instantiations(self) -> bool {
        self != Self::AllCandidates
    }

    pub fn explores_all_matches(self) -> bool {
        self != Self::AllCandidates
    }

    pub fn selected_instantiation_limit(self) -> Option<usize> {
        self.explores_all_matches().then_some(1)
    }
}

#[cfg(test)]
mod tests {
    use super::CandidateScope;

    #[test]
    fn staged_scope_centralizes_refinement_policy() {
        let scope = CandidateScope::SourceThenDerived;

        assert!(scope.allows_derived());
        assert!(scope.combines_provenance_catalogs());
        assert!(scope.tracks_provenance());
        assert!(scope.prefers_source_on_cost_tie());
        assert!(scope.requires_model_violation());
        assert!(scope.retries_rejected_instantiations());
        assert!(scope.explores_all_matches());
        assert_eq!(scope.selected_instantiation_limit(), Some(1));
    }

    #[test]
    fn legacy_full_scope_keeps_batch_behavior() {
        let scope = CandidateScope::AllCandidates;

        assert!(scope.allows_derived());
        assert!(!scope.combines_provenance_catalogs());
        assert!(!scope.tracks_provenance());
        assert!(!scope.prefers_source_on_cost_tie());
        assert!(!scope.requires_model_violation());
        assert!(!scope.retries_rejected_instantiations());
        assert!(!scope.explores_all_matches());
        assert_eq!(scope.selected_instantiation_limit(), None);
    }
}
