use std::collections::HashMap;

use egg::Language;
use rustc_hash::FxHashSet;
use smt2parser::vmt::{ReadsAndWrites, VARIABLE_FRAME_DELIMITER};

use crate::{
    cost_functions::YardbirdCostFunction,
    theories::array::array_axioms::{ArrayExpr, ArrayLanguage},
    training::{
        canonical_term_hash, AbstractInstantiationRecord, CandidateRecord, DecisionRecord,
        TermFeatures,
    },
};

fn compare_terms_with_cost(
    left: (&ArrayExpr, u32),
    right: (&ArrayExpr, u32),
) -> std::cmp::Ordering {
    left.1
        .cmp(&right.1)
        .then_with(|| left.0.to_string().cmp(&right.0.to_string()))
}

pub struct ArrayTermExtractor<CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    term_map: HashMap<egg::Id, Vec<(ArrayExpr, CF::Cost)>>,
    cost_function: CF,
    refinement_step: u32,
    pub reads_and_writes: ReadsAndWrites,
    property_terms: FxHashSet<String>,
    transition_terms: FxHashSet<String>,
    depth: u16,
}

fn deindex_abstract_term(instantiation: &ArrayExpr) -> ArrayExpr {
    let nodes = instantiation
        .as_ref()
        .iter()
        .map(|node| match node {
            ArrayLanguage::Symbol(sym) => {
                let normalized = match sym.as_str().split_once(VARIABLE_FRAME_DELIMITER) {
                    Some((base, suffix)) if suffix.parse::<u32>().is_ok() => base.into(),
                    _ => *sym,
                };
                ArrayLanguage::Symbol(normalized)
            }
            _ => node.clone(),
        })
        .collect::<Vec<_>>();

    ArrayExpr::from(nodes)
}

impl<CF> ArrayTermExtractor<CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    pub fn new<N>(
        egraph: &egg::EGraph<ArrayLanguage, N>,
        mut cost_function: CF,
        refinement_step: u32,
        depth: u16,
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
            terms.sort_by(|(left_term, left_cost), (right_term, right_cost)| {
                compare_terms_with_cost((left_term, *left_cost), (right_term, *right_cost))
            });
        }

        let reads_and_writes = cost_function.get_reads_and_writes();
        let property_terms = cost_function.get_property_terms().into_iter().collect();
        let transition_terms = cost_function.get_transition_terms().into_iter().collect();

        Self {
            term_map,
            cost_function,
            refinement_step,
            reads_and_writes,
            property_terms,
            transition_terms,
            depth,
        }
    }

    pub fn ranked_candidates<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
    ) -> Vec<(ArrayExpr, i32)>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        if let Some(terms) = self.term_map.get(&egraph.find(eclass)) {
            return terms
                .iter()
                .map(|(term, cost)| (term.clone(), *cost as i32))
                .collect();
        }

        let mut fallback_cost = self.cost_function.clone();
        let extractor = egg::Extractor::new(egraph, fallback_cost.clone());
        let (_, expr) = extractor.find_best(eclass);
        let cost = fallback_cost.cost_rec(&expr) as i32;
        vec![(expr, cost)]
    }

    pub fn decision_record<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
        axiom_name: &str,
        slot_index: u32,
        chosen_term: &ArrayExpr,
    ) -> DecisionRecord
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let chosen_hash = canonical_term_hash(chosen_term);
        let mut candidates = self
            .ranked_candidates(egraph, eclass)
            .into_iter()
            .map(|(term, cost)| {
                let features =
                    TermFeatures::extract(&term, &self.property_terms, &self.transition_terms);
                CandidateRecord {
                    term: term.to_string(),
                    term_hash: canonical_term_hash(&term),
                    is_constant: features.is_constant,
                    is_variable: features.is_variable,
                    in_property_vocab: features.in_property_vocab,
                    in_transition_vocab: features.in_transition_vocab,
                    frame_index: features.frame_index,
                    ast_size: features.ast_size,
                    current_cost: cost,
                    was_chosen: canonical_term_hash(&term) == chosen_hash,
                }
            })
            .collect::<Vec<_>>();

        // The specialized Read/Write reconstruction path can choose a term that did not come
        // from the ranked term-map candidates. When that happens, append the chosen term so the
        // provenance chain still has an explicit "winner" candidate to point to.
        if !candidates.iter().any(|candidate| candidate.was_chosen) {
            let features =
                TermFeatures::extract(chosen_term, &self.property_terms, &self.transition_terms);
            candidates.push(CandidateRecord {
                term: chosen_term.to_string(),
                term_hash: chosen_hash.clone(),
                is_constant: features.is_constant,
                is_variable: features.is_variable,
                in_property_vocab: features.in_property_vocab,
                in_transition_vocab: features.in_transition_vocab,
                frame_index: features.frame_index,
                ast_size: features.ast_size,
                current_cost: {
                    let mut cost_fn = self.cost_function.clone();
                    cost_fn.cost_rec(chosen_term) as i32
                },
                was_chosen: true,
            });
        }

        DecisionRecord {
            decision_key: format!(
                "{}:{}:{}:{}:{}",
                axiom_name, self.depth, self.refinement_step, slot_index, eclass
            ),
            bmc_depth: self.depth,
            axiom_name: axiom_name.to_string(),
            slot_index,
            candidates,
        }
    }

    pub fn abstract_instantiation_record(
        &self,
        axiom_name: &str,
        ordinal: usize,
        instantiation: &ArrayExpr,
        decision_keys: Vec<String>,
    ) -> AbstractInstantiationRecord {
        let abstract_term = deindex_abstract_term(instantiation);
        AbstractInstantiationRecord {
            abstract_instantiation_id: format!(
                "{}:{}:{}:{}",
                axiom_name, self.depth, self.refinement_step, ordinal
            ),
            term: abstract_term.to_string(),
            term_hash: canonical_term_hash(instantiation),
            axiom_name: axiom_name.to_string(),
            bmc_depth: self.depth,
            refinement_step: self.refinement_step,
            decision_keys,
            in_unsat_core: false,
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

#[cfg(test)]
mod tests {
    use super::{compare_terms_with_cost, deindex_abstract_term, ArrayTermExtractor};
    use crate::{
        cost_functions::YardbirdCostFunction,
        theories::array::array_axioms::{ArrayExpr, ArrayLanguage},
    };
    use smt2parser::vmt::ReadsAndWrites;

    #[derive(Clone)]
    struct ZeroCostTerms {
        terms: Vec<ArrayExpr>,
    }

    impl egg::CostFunction<ArrayLanguage> for ZeroCostTerms {
        type Cost = u32;

        fn cost<C>(&mut self, _enode: &ArrayLanguage, _costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            0
        }
    }

    impl YardbirdCostFunction<ArrayLanguage> for ZeroCostTerms {
        fn get_string_terms(&self) -> Vec<String> {
            self.terms.iter().map(ToString::to_string).collect()
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }

        fn get_parsed_terms(&self) -> Vec<egg::RecExpr<ArrayLanguage>> {
            self.terms.clone()
        }
    }

    #[test]
    fn deindex_abstract_term_removes_frame_suffixes() {
        let expr: ArrayExpr =
            "(= (Read Int Int (Write Int Int b@2 i@2 (Read Int Int a@2 i@2)) Z@3) (Read Int Int b@2 Z@3))"
                .parse()
                .unwrap();

        let normalized = deindex_abstract_term(&expr).to_string();

        assert!(!normalized.contains("@"));
        assert_eq!(
            normalized,
            "(= (Read Int Int (Write Int Int b i (Read Int Int a i)) Z) (Read Int Int b Z))"
        );
    }

    #[test]
    fn compare_terms_with_cost_breaks_ties_lexicographically() {
        let a: ArrayExpr = "a".parse().unwrap();
        let b: ArrayExpr = "b".parse().unwrap();

        assert!(compare_terms_with_cost((&a, 1), (&b, 1)).is_lt());
        assert!(compare_terms_with_cost((&b, 0), (&a, 1)).is_lt());
    }

    #[test]
    fn extractor_uses_deterministic_order_for_equal_cost_terms() {
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        let b: ArrayExpr = "b".parse().unwrap();
        let a: ArrayExpr = "a".parse().unwrap();
        let b_id = egraph.add_expr(&b);
        let a_id = egraph.add_expr(&a);
        egraph.union(b_id, a_id);
        egraph.rebuild();

        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCostTerms {
                terms: vec![b.clone(), a.clone()],
            },
            0,
            0,
        );

        assert_eq!(extractor.extract(&egraph, b_id).to_string(), "a");
    }
}
