pub mod array;
pub mod bvlist;
pub mod list;

use egg::CostFunction;
use smt2parser::vmt::ReadsAndWrites;

pub trait YardbirdCostFunction<L>: CostFunction<L, Cost = u32> + Clone
where
    L: egg::Language,
{
    fn get_string_terms(&self) -> Vec<String>;
    fn get_reads_and_writes(&self) -> ReadsAndWrites;
}
