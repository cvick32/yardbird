use std::collections::HashMap;

use egg::Language;
use smt2parser::vmt::ReadsAndWrites;

use crate::array_axioms::ArrayLanguage;

pub struct TermExtractor<'a, CF, N>
where
    CF: egg::CostFunction<ArrayLanguage>,
    N: egg::Analysis<ArrayLanguage>,
{
    egraph: &'a egg::EGraph<ArrayLanguage, N>,
    extractor: egg::Extractor<'a, CF, ArrayLanguage, N>,
    term_map: HashMap<egg::Id, Vec<egg::RecExpr<ArrayLanguage>>>,
    pub reads_and_writes: &'a ReadsAndWrites,
}

impl<'a, CF, N> TermExtractor<'a, CF, N>
where
    CF: egg::CostFunction<ArrayLanguage>,
    N: egg::Analysis<ArrayLanguage>,
    <CF as egg::CostFunction<ArrayLanguage>>::Cost: Ord,
{
    pub fn new(
        egraph: &'a egg::EGraph<ArrayLanguage, N>,
        mut cost_function: CF,
        transition_system_terms: &'a [String],
        _property_terms: &'a [String],
        reads_and_writes: &'a ReadsAndWrites,
    ) -> Self {
        let mut term_map: HashMap<egg::Id, Vec<egg::RecExpr<ArrayLanguage>>> = HashMap::new();
        for string_term in transition_system_terms {
            let term: egg::RecExpr<ArrayLanguage> = string_term.parse().unwrap();
            match egraph.lookup_expr(&term) {
                // TODO: might want to keep track of all terms that match this node
                Some(expr) => term_map
                    .entry(expr)
                    .and_modify(|v: &mut _| v.push(term.clone()))
                    .or_insert_with(|| vec![term]),
                None => continue,
            };
        }

        // sort terms by cost function so that the first one is the lowest cost
        for exprs in term_map.values_mut() {
            exprs.sort_by_key(|expr| cost_function.cost_rec(expr));
        }

        let extractor = egg::Extractor::new(egraph, cost_function);

        Self {
            egraph,
            extractor,
            term_map,
            reads_and_writes,
        }
    }

    pub fn extract(&self, eclass: egg::Id) -> egg::RecExpr<ArrayLanguage> {
        // let is_potential_read = self.egraph[eclass]
        //     .parents()
        //     .any(|(node, _parent_id)| matches!(node, ArrayLanguage::Read(_)));

        if let Some(terms) = self.term_map.get(&self.egraph.find(eclass)) {
            log::debug!("term exists: {eclass} -> {}", terms[0]);
            terms[0].clone()
        } else {
            let node = self.extractor.find_best_node(eclass);
            log::debug!("recursing: {eclass} -> {node}");
            node.join_recexprs(|id| self.extract(id))
        }
    }
}
