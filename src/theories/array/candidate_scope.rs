//! Eligibility policy for terms considered during array-axiom matching.
//!
//! Candidate scope answers which representatives may participate and how far
//! matching must search. It deliberately does not score terms or complete
//! instantiations; those decisions belong to the configured cost function.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateScope {
    SourceGroundedOnly,
    AllCandidates,
}

impl CandidateScope {
    pub fn requires_source_grounded(self) -> bool {
        self == Self::SourceGroundedOnly
    }

    pub fn allows_derived(self) -> bool {
        self == Self::AllCandidates
    }

    pub fn tracks_provenance(self) -> bool {
        self == Self::SourceGroundedOnly
    }

    /// Source provenance is a deterministic tie-breaker, never a substitute
    /// for the configured term cost.
    pub fn prefers_source_on_cost_tie(self) -> bool {
        self == Self::SourceGroundedOnly
    }

    pub fn requires_model_violation(self) -> bool {
        self == Self::SourceGroundedOnly
    }

    pub fn explores_all_matches(self) -> bool {
        self == Self::SourceGroundedOnly
    }
}
