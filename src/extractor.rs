use std::{cmp::Ordering, collections::HashMap};

use egg::*;

fn cmp<T: PartialOrd>(a: &Option<T>, b: &Option<T>) -> Ordering {
    // None is high
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(a), Some(b)) => a.partial_cmp(b).unwrap(),
    }
}

#[derive(Debug)]
pub struct Extractor<'a, CF: CostFunction<L>, L: Language, N: Analysis<L>> {
    cost_function: CF,
    costs: HashMap<Id, (CF::Cost, L)>,
    egraph: &'a EGraph<L, N>,
    term_map: HashMap<Id, egg::RecExpr<L>>,
}

impl<'a, CF, L, N> Extractor<'a, CF, L, N>
where
    CF: CostFunction<L>,
    L: Language + FromOp + std::fmt::Display,
    N: Analysis<L>,
{
    /// Create a new `Extractor` given an `EGraph` and a
    /// `CostFunction`.
    ///
    /// The extraction does all the work on creation, so this function
    /// performs the greedy search for cheapest representative of each
    /// eclass.
    pub fn new(
        egraph: &'a EGraph<L, N>,
        cost_function: CF,
        transition_system_terms: &'a [String],
        _property_terms: &'a [String],
    ) -> Self {
        let costs = HashMap::default();
        let mut term_map = HashMap::new();
        for string_term in transition_system_terms {
            println!("{string_term}");
            let term: egg::RecExpr<L> = string_term.parse().unwrap();
            match egraph.lookup_expr(&term) {
                // TODO: might want to keep track of all terms that match this node
                Some(expr) => term_map.insert(expr, term),
                None => todo!(),
            };
        }
        // for string_term in property_terms {
        //     let term: egg::RecExpr<L> = string_term.parse().unwrap();
        //     match egraph.lookup_expr(&term) {
        //         Some(expr) => term_map.insert(expr, term),
        //         None => todo!(),
        //     };
        // }

        term_map
            .iter()
            .for_each(|(id, term)| println!("{id} -> {}", term.pretty(80)));

        let mut extractor = Extractor {
            costs,
            egraph,
            cost_function,
            term_map,
        };
        extractor.find_costs();

        extractor
    }

    pub fn extract(&self, eclass: Id) -> RecExpr<L> {
        let (_cost, root) = self.costs[&self.egraph.find(eclass)].clone();

        root.join_recexprs(|id| self.find_best_term(id))
    }

    /// Find the cheapest (lowest cost) represented `RecExpr` in the
    /// given eclass.
    // pub fn find_best(&self, eclass: Id) -> (CF::Cost, RecExpr<L>) {
    //     let (cost, root) = self.costs[&self.egraph.find(eclass)].clone();
    //     let expr = root.build_recexpr(|id| self.find_best_node(id).clone());
    //     (cost, expr)
    // }

    /// Find the cheapest e-node in the given e-class.
    pub fn find_best_term(&self, eclass: Id) -> RecExpr<L> {
        if let Some(term) = self.term_map.get(&eclass) {
            term.clone()
        } else {
            self.find_best_node(eclass)
                .join_recexprs(|id| self.find_best_term(id))
        }
    }

    pub fn find_best_node(&self, eclass: Id) -> &L {
        &self.costs[&self.egraph.find(eclass)].1
    }

    /// Find the cost of the term that would be extracted from this e-class.
    // pub fn find_best_cost(&self, eclass: Id) -> CF::Cost {
    //     let (cost, _) = &self.costs[&self.egraph.find(eclass)];
    //     cost.clone()
    // }

    fn node_total_cost(&mut self, node: &L) -> Option<CF::Cost> {
        let eg = &self.egraph;
        let has_cost = |id| self.costs.contains_key(&eg.find(id));
        if node.all(has_cost) {
            let costs = &self.costs;
            let cost_f = |id| costs[&eg.find(id)].0.clone();
            Some(self.cost_function.cost(node, cost_f))
        } else {
            None
        }
    }

    fn find_costs(&mut self) {
        let mut did_something = true;
        while did_something {
            did_something = false;

            for class in self.egraph.classes() {
                let pass = self.make_pass(class);
                match (self.costs.get(&class.id), pass) {
                    (None, Some(new)) => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    (Some(old), Some(new)) if new.0 < old.0 => {
                        self.costs.insert(class.id, new);
                        did_something = true;
                    }
                    _ => (),
                }
            }
        }

        for class in self.egraph.classes() {
            if !self.costs.contains_key(&class.id) {
                log::warn!(
                    "Failed to compute cost for eclass {}: {:?}",
                    class.id,
                    class.nodes
                )
            }
        }
    }

    fn make_pass(&mut self, eclass: &EClass<L, N::Data>) -> Option<(CF::Cost, L)> {
        let (cost, node) = eclass
            .iter()
            .map(|n| (self.node_total_cost(n), n.clone()))
            .min_by(|a, b| cmp(&a.0, &b.0))
            .unwrap_or_else(|| panic!("Can't extract, eclass is empty: {:#?}", eclass));
        cost.map(|c| (c, node.clone()))
    }
}
