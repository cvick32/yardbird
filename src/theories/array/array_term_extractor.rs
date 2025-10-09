use std::collections::HashMap;

use egg::Language;
use smt2parser::vmt::ReadsAndWrites;

use crate::{
    cost_functions::YardbirdCostFunction,
    theories::array::array_axioms::{ArrayExpr, ArrayLanguage},
};

pub struct ArrayTermExtractor<CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    term_map: HashMap<egg::Id, Vec<(ArrayExpr, CF::Cost)>>,
    cost_function: CF,
    refinement_step: u32,
    pub reads_and_writes: ReadsAndWrites,
}

impl<CF> ArrayTermExtractor<CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    pub fn new<N>(
        egraph: &egg::EGraph<ArrayLanguage, N>,
        mut cost_function: CF,
        refinement_step: u32,
    ) -> Self
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let mut term_map: HashMap<egg::Id, Vec<_>> = HashMap::new();

        // Use pre-parsed terms to avoid parsing in hot path
        for term in cost_function.get_parsed_terms() {
            let cost = cost_function.cost_rec(&term);
            match egraph.lookup_expr(&term) {
                // TODO: might want to keep track of all terms that match this node
                Some(expr) => term_map
                    .entry(expr)
                    .and_modify(|v: &mut _| v.push((term.clone(), cost)))
                    .or_insert_with(|| vec![(term, cost)]),
                None => continue,
            };
        }

        // Pre-sort all term vectors by cost for faster extraction
        for terms in term_map.values_mut() {
            terms.sort_by_key(|(_, cost)| *cost);
        }

        let reads_and_writes = cost_function.get_reads_and_writes();

        Self {
            term_map,
            cost_function,
            refinement_step,
            reads_and_writes,
        }
    }

    pub fn extract<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
    ) -> egg::RecExpr<ArrayLanguage>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        if let Some(terms) = self.term_map.get(&egraph.find(eclass)) {
            log::debug!("NUMBER OF OPTIONS: {}", terms.len());

            // Terms are already sorted by cost, use direct indexing
            if let Some((term, cost)) = terms.get(self.refinement_step as usize) {
                log::debug!(
                    "term #{}: {eclass} -> {}={}",
                    self.refinement_step,
                    term,
                    cost
                );
                return term.clone();
            }

            // Fallback to best (first) term if refinement_step is out of bounds
            if let Some((best_term, best_cost)) = terms.first() {
                log::debug!("Just using best_term: {} cost: {}", best_term, best_cost);
                return best_term.clone();
            }
        }

        // No terms in map, fall back to standard extraction
        let extractor = egg::Extractor::new(egraph, self.cost_function.clone());
        let node = extractor.find_best_node(eclass);
        log::debug!("recursing: {eclass} -> {node}");
        node.join_recexprs(|id| self.extract(egraph, id))
    }
}
