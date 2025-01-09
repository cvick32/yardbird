use std::collections::HashMap;

pub struct TermExtractor<'a, CF, L, N>
where
    CF: egg::CostFunction<L>,
    L: egg::Language,
    N: egg::Analysis<L>,
{
    egraph: &'a egg::EGraph<L, N>,
    extractor: egg::Extractor<'a, CF, L, N>,
    term_map: HashMap<egg::Id, Vec<egg::RecExpr<L>>>,
}

impl<'a, CF, L, N> TermExtractor<'a, CF, L, N>
where
    CF: egg::CostFunction<L>,
    L: egg::Language + egg::FromOp + std::fmt::Display,
    N: egg::Analysis<L>,
    <CF as egg::CostFunction<L>>::Cost: Ord,
{
    pub fn new(
        egraph: &'a egg::EGraph<L, N>,
        mut cost_function: CF,
        transition_system_terms: &'a [String],
        _property_terms: &'a [String],
    ) -> Self {
        let mut term_map: HashMap<egg::Id, Vec<egg::RecExpr<L>>> = HashMap::new();
        for string_term in transition_system_terms {
            let term: egg::RecExpr<L> = string_term.parse().unwrap();
            match egraph.lookup_expr(&term) {
                // TODO: might want to keep track of all terms that match this node
                Some(expr) => term_map
                    .entry(expr)
                    .and_modify(|v: &mut _| v.push(term.clone()))
                    .or_insert_with(|| vec![term]),
                None => todo!(),
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
        }
    }

    pub fn extract(&self, eclass: egg::Id) -> egg::RecExpr<L> {
        if let Some(terms) = self.term_map.get(&self.egraph.find(eclass)) {
            terms[0].clone()
        } else {
            self.extractor
                .find_best_node(eclass)
                .join_recexprs(|id| self.extract(id))
        }
    }
}
