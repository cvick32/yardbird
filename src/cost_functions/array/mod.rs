use crate::{
    cost_functions::YardbirdCostFunction, problem_context::ProblemContext,
    theories::array::array_axioms::ArrayLanguage,
};

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

pub trait ArrayCostFactory: YardbirdCostFunction<ArrayLanguage> + Sized {
    type Config: Clone + Send + Sync + 'static;

    fn from_context(smt: &dyn ProblemContext, depth: u32, config: &Self::Config) -> Self;
}
