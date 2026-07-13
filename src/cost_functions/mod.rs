pub mod array;
pub mod bvlist;
pub mod list;

use egg::CostFunction;
use smt2parser::vmt::ReadsAndWrites;

use crate::theories::array::array_axioms::ArrayExpr;

#[derive(Clone, Copy, Debug)]
pub struct CandidateChoiceContext<'a> {
    pub axiom_name: &'a str,
    pub slot_index: u32,
    pub bmc_depth: u16,
}

#[derive(Clone, Copy, Debug)]
pub struct CandidateChoice<'a> {
    pub term: &'a ArrayExpr,
    pub current_cost: u32,
    pub cost_rank: usize,
    pub cost_rank_frac: f64,
    pub candidate_count: usize,
    pub prior_use_count: u32,
}

pub trait YardbirdCostFunction<L>: CostFunction<L, Cost = u32> + Clone
where
    L: egg::Language + egg::FromOp,
{
    fn get_string_terms(&self) -> Vec<String>;
    fn get_transition_terms(&self) -> Vec<String> {
        vec![]
    }
    fn get_property_terms(&self) -> Vec<String> {
        vec![]
    }
    fn get_reads_and_writes(&self) -> ReadsAndWrites;

    fn choose_candidate_with_ml(
        &self,
        _context: &CandidateChoiceContext<'_>,
        _candidates: &[CandidateChoice<'_>],
    ) -> Option<usize> {
        None
    }

    /// Get pre-parsed terms as RecExprs. Default implementation parses from strings,
    /// but implementations can override for better performance.
    fn get_parsed_terms(&self) -> Vec<egg::RecExpr<L>> {
        self.get_string_terms()
            .into_iter()
            .filter_map(|s| s.parse().ok())
            .collect()
    }
}
