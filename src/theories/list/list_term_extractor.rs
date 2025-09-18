use std::collections::HashMap;

use egg::Language;
use smt2parser::vmt::ReadsAndWrites;

use crate::{
    cost_functions::YardbirdCostFunction,
    theories::list::list_axioms::{ListExpr, ListLanguage},
};

pub struct ListTermExtractor<CF>
where
    CF: YardbirdCostFunction<ListLanguage>,
{
    term_map: HashMap<egg::Id, Vec<(ListExpr, CF::Cost)>>,
    cost_function: CF,
    pub reads_and_writes: ReadsAndWrites,
}

impl<CF> ListTermExtractor<CF>
where
    CF: YardbirdCostFunction<ListLanguage>,
{
    pub fn new<N>(egraph: &egg::EGraph<ListLanguage, N>, mut cost_function: CF) -> Self
    where
        N: egg::Analysis<ListLanguage>,
    {
        let mut term_map: HashMap<egg::Id, Vec<_>> = HashMap::new();
        for string_term in cost_function.get_string_terms() {
            let term: egg::RecExpr<ListLanguage> = string_term.parse().unwrap();
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
            reads_and_writes,
        }
    }

    pub fn extract<N>(
        &self,
        egraph: &egg::EGraph<ListLanguage, N>,
        eclass: egg::Id,
    ) -> egg::RecExpr<ListLanguage>
    where
        N: egg::Analysis<ListLanguage>,
    {
        if let Some(terms) = self.term_map.get(&egraph.find(eclass)) {
            let (best_term, _) = terms.iter().min_by_key(|(_term, cost)| cost).unwrap();
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
