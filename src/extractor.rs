use std::collections::HashMap;

use egg::Language;
use smt2parser::vmt::ReadsAndWrites;

use crate::array_axioms::{ArrayExpr, ArrayLanguage};

pub struct TermExtractor<CF>
where
    CF: egg::CostFunction<ArrayLanguage>,
{
    term_map: HashMap<egg::Id, Vec<(ArrayExpr, CF::Cost)>>,
    cost_function: CF,
    pub reads_and_writes: ReadsAndWrites,
}

impl<CF> TermExtractor<CF>
where
    CF: egg::CostFunction<ArrayLanguage> + Clone,
    <CF as egg::CostFunction<ArrayLanguage>>::Cost: Ord,
{
    pub fn new<N>(
        egraph: &egg::EGraph<ArrayLanguage, N>,
        mut cost_function: CF,
        transition_system_terms: &[String],
        property_terms: &[String],
        reads_and_writes: ReadsAndWrites,
    ) -> Self
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let mut term_map: HashMap<egg::Id, Vec<_>> = HashMap::new();
        for string_term in transition_system_terms.iter().chain(property_terms) {
            let term: egg::RecExpr<ArrayLanguage> = string_term.parse().unwrap();
            let cost = cost_function.cost_rec(&term);
            match egraph.lookup_expr(&term) {
                // TODO: might want to keep track of all terms that match this node
                Some(expr) => term_map
                    .entry(expr)
                    .and_modify(|v: &mut _| v.push((term.clone(), cost.clone())))
                    .or_insert_with(|| vec![(term, cost)]),
                None => continue,
            };
        }

        // sort terms by cost function so that the first one is the lowest cost
        // for exprs in term_map.values_mut() {
        //     exprs.sort_by_key(|(_expr, cost)| cost.clone());
        // }

        Self {
            term_map,
            cost_function,
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
            let (best_term, _) = terms
                .iter()
                .min_by_key(|(_term, cost)| cost.clone())
                .unwrap();
            log::debug!("term exists: {eclass} -> {}", best_term);
            best_term.clone()
        } else {
            let extractor = egg::Extractor::new(egraph, self.cost_function.clone());
            let node = extractor.find_best_node(eclass);
            log::debug!("recursing: {eclass} -> {node}");
            node.join_recexprs(|id| self.extract(egraph, id))
        }
    }
}
