use std::collections::HashMap;

use egg::Language;
use itertools::Itertools;
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
        for string_term in cost_function.get_string_terms() {
            let term: egg::RecExpr<ArrayLanguage> = string_term.parse().unwrap();
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
            log::info!("NUMBER OF OPTIONS: {}", terms.len());
            for (i, term) in terms.iter().sorted_by_key(|(_term, cost)| cost).enumerate() {
                log::info!("{i}/{}", self.refinement_step);
                log::info!("term: {} cost: {}", term.0, term.1);
                if i == self.refinement_step as usize {
                    log::info!("term #{i}: {eclass} -> {}={}", term.0, term.1);
                    return term.0.clone();
                }
            }
            let (best_term, _) = terms.iter().min_by_key(|(_term, cost)| cost).unwrap();
            log::info!("Just using best_term: {}", best_term);
            best_term.clone()
        } else {
            let extractor = egg::Extractor::new(egraph, self.cost_function.clone());
            let node = extractor.find_best_node(eclass);
            log::info!("recursing: {eclass} -> {node}");
            node.join_recexprs(|id| self.extract(egraph, id))
        }
    }
}
