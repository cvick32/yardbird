pub mod array;
pub mod bvlist;
pub mod list;

use egg::CostFunction;
use smt2parser::vmt::ReadsAndWrites;

pub trait YardbirdCostFunction<L>: CostFunction<L, Cost = u32> + Clone
where
    L: egg::Language + egg::FromOp,
{
    fn get_string_terms(&self) -> Vec<String>;
    fn get_reads_and_writes(&self) -> ReadsAndWrites;

    /// Get pre-parsed terms as RecExprs. Default implementation parses from strings,
    /// but implementations can override for better performance.
    fn get_parsed_terms(&self) -> Vec<egg::RecExpr<L>> {
        self.get_string_terms()
            .into_iter()
            .filter_map(|s| s.parse().ok())
            .collect()
    }
}
