pub mod array;
pub mod bvlist;
pub mod list;

use egg::CostFunction;
use smt2parser::vmt::ReadsAndWrites;

use crate::quantified_rule::QuantifiedRuleCategory;

#[derive(Clone, Copy, Debug)]
pub struct CandidateSelectionContext<'a> {
    pub rule_name: &'a str,
    pub rule_category: QuantifiedRuleCategory,
    pub variable: &'a str,
    pub bmc_depth: u16,
}

#[derive(Clone, Debug)]
pub struct CandidateView<'a, L>
where
    L: egg::Language,
{
    pub expression: &'a egg::RecExpr<L>,
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

    /// Optionally select one candidate using the complete quantified-rule
    /// context. Returning `None` delegates to the caller's deterministic
    /// cost-based fallback.
    fn select_candidate(
        &self,
        _context: &CandidateSelectionContext<'_>,
        _candidates: &[CandidateView<'_, L>],
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
