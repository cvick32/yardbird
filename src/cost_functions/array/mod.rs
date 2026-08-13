use crate::{
    cost_functions::YardbirdCostFunction,
    problem_context::{ArrayCandidateCatalog, ProblemContext},
    theories::array::{array_axioms::ArrayLanguage, candidate_scope::CandidateScope},
};
use smt2parser::vmt::ReadsAndWrites;

pub mod adaptive_cost;
pub mod ast_size;
pub mod generated;
pub mod index_aware_cost;
pub mod logistic_regression;
pub mod prefer_constants;
pub mod prefer_read;
pub mod prefer_write;
pub mod split_cost;
pub mod symbol_cost;

pub use adaptive_cost::AdaptiveArrayCost;
pub use ast_size::ArrayAstSize;
pub use generated::ArrayGenerated;
pub use index_aware_cost::IndexAwareArrayCost;
pub use logistic_regression::LogisticRegression;
pub use prefer_constants::ArrayPreferConstants;
pub use prefer_read::ArrayPreferRead;
pub use prefer_write::ArrayPreferWrite;
pub use split_cost::SplitArrayCost;
pub use symbol_cost::ArrayBMCCost;

/// The candidate vocabulary visible while constructing an array cost function.
///
/// Cone builders receive only source-grounded vocabulary. The legacy full
/// builder receives the historical merged vocabulary, preserving its baseline.
pub struct ArrayCostContext {
    init_and_transition_subterms: Vec<String>,
    property_subterms: Vec<String>,
    reads_and_writes: ReadsAndWrites,
}

impl ArrayCostContext {
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

pub trait ArrayCostFactory: YardbirdCostFunction<ArrayLanguage> + Sized {
    type Config: Clone + Send + Sync + 'static;

    fn from_context(smt: &ArrayCostContext, depth: u32, config: &Self::Config) -> Self;
}
