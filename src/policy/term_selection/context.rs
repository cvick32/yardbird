//! Vocabulary supplied to term-selection policies.
use crate::problem_context::{ArrayCandidateCatalog, ProblemContext};
use crate::rule_matching::scope::CandidateScope;
use smt2parser::vmt::ReadsAndWrites;

/// The candidate vocabulary visible while constructing an array cost function.
///
/// Cone builders receive only source-grounded vocabulary. The legacy full
/// builder receives the historical merged vocabulary, preserving its baseline.
#[derive(Default)]
pub struct TermCostContext {
    init_and_transition_subterms: Vec<String>,
    property_subterms: Vec<String>,
    reads_and_writes: ReadsAndWrites,
}

impl TermCostContext {
    pub(crate) fn source_vocabulary(
        init_and_transition_subterms: Vec<String>,
        property_subterms: Vec<String>,
        reads_and_writes: ReadsAndWrites,
    ) -> Self {
        Self {
            init_and_transition_subterms,
            property_subterms,
            reads_and_writes,
        }
    }
    pub fn from_problem(
        smt: &dyn ProblemContext,
        candidates: &ArrayCandidateCatalog,
        scope: CandidateScope,
    ) -> Self {
        if scope.requires_source_grounded() {
            Self {
                init_and_transition_subterms: smt.get_source_init_and_transition_subterms(),
                property_subterms: smt.get_property_subterms(),
                reads_and_writes: candidates.source_grounded.reads_and_writes.clone(),
            }
        } else {
            Self {
                init_and_transition_subterms: smt.get_init_and_transition_subterms(),
                property_subterms: smt.get_property_subterms(),
                reads_and_writes: smt.get_reads_and_writes(),
            }
        }
    }

    pub fn get_init_and_transition_subterms(&self) -> Vec<String> {
        self.init_and_transition_subterms.clone()
    }

    pub fn get_property_subterms(&self) -> Vec<String> {
        self.property_subterms.clone()
    }

    pub fn get_reads_and_writes(&self) -> ReadsAndWrites {
        self.reads_and_writes.clone()
    }
}
