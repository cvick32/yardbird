use std::collections::HashMap;

use egg::Language;
use rustc_hash::{FxHashMap, FxHashSet};
use smt2parser::vmt::{ReadsAndWrites, VARIABLE_FRAME_DELIMITER};

use crate::{
    cost_functions::{CandidateChoice, CandidateChoiceContext, YardbirdCostFunction},
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

fn prior_use_count(selection_counts: &FxHashMap<String, u32>, term: &ArrayExpr) -> u32 {
    selection_counts
        .get(&canonical_term_hash(term))
        .copied()
        .unwrap_or(0)
}

fn compare_terms_with_history(
    left: (&ArrayExpr, u32),
    right: (&ArrayExpr, u32),
    selection_counts: &FxHashMap<String, u32>,
    baseline_use_count: u32,
) -> std::cmp::Ordering {
    let left_penalty = prior_use_count(selection_counts, left.0).saturating_sub(baseline_use_count);
    let right_penalty =
        prior_use_count(selection_counts, right.0).saturating_sub(baseline_use_count);

    left.1
        .saturating_add(left_penalty)
        .cmp(&right.1.saturating_add(right_penalty))
        .then_with(|| compare_terms_with_cost(left, right))
}

fn is_z3_model_value_node(node: &ArrayLanguage) -> bool {
    matches!(node, ArrayLanguage::Symbol(symbol) if symbol.as_str().contains("!val!"))
}

fn contains_z3_model_value(expr: &ArrayExpr) -> bool {
    expr.as_ref().iter().any(is_z3_model_value_node)
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
    selection_counts: FxHashMap<String, u32>,
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
        selection_counts: FxHashMap<String, u32>,
        depth: u16,
    ) -> Self
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let mut term_map: HashMap<egg::Id, Vec<_>> = HashMap::new();

        // Use pre-parsed terms to avoid parsing in hot path
        for term in cost_function.get_parsed_terms() {
            if contains_z3_model_value(&term) {
                continue;
            }
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
            selection_counts,
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
            let candidates = terms
                .iter()
                .filter(|(term, _)| !contains_z3_model_value(term))
                .map(|(term, cost)| (term.clone(), *cost as i32))
                .collect::<Vec<_>>();
            if !candidates.is_empty() {
                return candidates;
            }
        }

        self.extract_from_egraph(egraph, eclass)
            .map(|expr| {
                let cost = self.cost_of(&expr) as i32;
                vec![(expr, cost)]
            })
            .unwrap_or_default()
    }

    pub fn cost_of(&self, expr: &ArrayExpr) -> u32 {
        let mut cost_fn = self.cost_function.clone();
        cost_fn.cost_rec(expr)
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

    fn candidate_ranks(
        &self,
        valid_terms: &[&(ArrayExpr, u32)],
    ) -> FxHashMap<String, (usize, f64)> {
        let candidate_count = valid_terms.len();
        let mut ranked_terms = valid_terms
            .iter()
            .map(|entry| {
                let (term, cost) = *entry;
                (term, *cost)
            })
            .collect::<Vec<_>>();

        ranked_terms.sort_by(|(left_term, left_cost), (right_term, right_cost)| {
            left_cost
                .cmp(right_cost)
                .then_with(|| left_term.as_ref().len().cmp(&right_term.as_ref().len()))
                .then_with(|| canonical_term_hash(left_term).cmp(&canonical_term_hash(right_term)))
                .then_with(|| left_term.to_string().cmp(&right_term.to_string()))
        });

        let mut ranks = FxHashMap::default();
        for (index, (term, _)) in ranked_terms.into_iter().enumerate() {
            let cost_rank = index + 1;
            let cost_rank_frac = if candidate_count <= 1 {
                0.0
            } else {
                index as f64 / (candidate_count - 1) as f64
            };
            ranks
                .entry(canonical_term_hash(term))
                .or_insert((cost_rank, cost_rank_frac));
        }
        ranks
    }

    fn choose_candidate_with_ml<'a>(
        &self,
        valid_terms: &[&'a (ArrayExpr, u32)],
        axiom_name: &str,
        slot_index: u32,
    ) -> Option<(&'a ArrayExpr, u32)> {
        let candidate_count = valid_terms.len();
        if candidate_count == 0 {
            return None;
        }

        let ranks = self.candidate_ranks(valid_terms);
        let choices = valid_terms
            .iter()
            .map(|entry| {
                let (term, cost) = *entry;
                let (cost_rank, cost_rank_frac) = ranks
                    .get(&canonical_term_hash(term))
                    .copied()
                    .unwrap_or((candidate_count, 1.0));
                CandidateChoice {
                    term,
                    current_cost: *cost,
                    cost_rank,
                    cost_rank_frac,
                    candidate_count,
                    prior_use_count: prior_use_count(&self.selection_counts, term),
                }
            })
            .collect::<Vec<_>>();
        let context = CandidateChoiceContext {
            axiom_name,
            slot_index,
            bmc_depth: self.depth,
        };
        let chosen_index = self
            .cost_function
            .choose_candidate_with_ml(&context, &choices)?;
        if chosen_index >= choices.len() {
            log::warn!(
                "ML candidate chooser returned out-of-range index {} for {} candidates",
                chosen_index,
                choices.len()
            );
            return None;
        }
        let chosen = choices[chosen_index];
        Some((chosen.term, chosen.current_cost))
    }

    fn choose_with_history<'a>(
        &self,
        valid_terms: Vec<&'a (ArrayExpr, u32)>,
        baseline_use_count: u32,
    ) -> Option<(&'a ArrayExpr, u32)> {
        valid_terms
            .into_iter()
            .min_by(|(left_term, left_cost), (right_term, right_cost)| {
                compare_terms_with_history(
                    (left_term, *left_cost),
                    (right_term, *right_cost),
                    &self.selection_counts,
                    baseline_use_count,
                )
            })
            .map(|(term, cost)| (term, *cost))
    }

    pub fn extract<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
    ) -> egg::RecExpr<ArrayLanguage>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        self.extract_for_decision(egraph, eclass, "unknown", 0)
    }

    pub fn extract_for_decision<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
        axiom_name: &str,
        slot_index: u32,
    ) -> egg::RecExpr<ArrayLanguage>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        if let Some(terms) = self.term_map.get(&egraph.find(eclass)) {
            log::debug!("NUMBER OF OPTIONS: {}", terms.len());
            let valid_terms = terms
                .iter()
                .filter(|(term, _)| !contains_z3_model_value(term))
                .collect::<Vec<_>>();
            let baseline_use_count = valid_terms
                .iter()
                .map(|(term, _)| prior_use_count(&self.selection_counts, term))
                .min()
                .unwrap_or(0);

            if let Some((term, cost)) =
                self.choose_candidate_with_ml(&valid_terms, axiom_name, slot_index)
            {
                let prior_uses = prior_use_count(&self.selection_counts, term);
                log::debug!(
                    "ml-chosen term: {eclass} -> {} base_cost={} prior_uses={} penalty={}",
                    term,
                    cost,
                    prior_uses,
                    prior_uses.saturating_sub(baseline_use_count)
                );
                return term.clone();
            }

            if let Some((term, cost)) = self.choose_with_history(valid_terms, baseline_use_count) {
                let prior_uses = prior_use_count(&self.selection_counts, term);
                log::debug!(
                    "history-aware term: {eclass} -> {} base_cost={} prior_uses={} penalty={}",
                    term,
                    cost,
                    prior_uses,
                    prior_uses.saturating_sub(baseline_use_count)
                );
                return term.clone();
            }
        }

        self.extract_from_egraph(egraph, eclass).unwrap_or_else(|| {
            panic!("No non-Z3-model representative available for e-class {eclass}")
        })
    }

    fn extract_from_egraph<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
    ) -> Option<ArrayExpr>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let mut memo = FxHashMap::default();
        let mut visiting = FxHashSet::default();
        self.extract_from_eclass(egraph, eclass, &mut memo, &mut visiting)
    }

    fn extract_from_eclass<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
        memo: &mut FxHashMap<egg::Id, Option<ArrayExpr>>,
        visiting: &mut FxHashSet<egg::Id>,
    ) -> Option<ArrayExpr>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let eclass = egraph.find(eclass);
        if let Some(cached) = memo.get(&eclass) {
            return cached.clone();
        }
        if !visiting.insert(eclass) {
            return None;
        }

        let mut best: Option<(u32, String, ArrayExpr)> = None;
        for node in &egraph[eclass].nodes {
            if is_z3_model_value_node(node) {
                continue;
            }

            let mut child_exprs = FxHashMap::default();
            let mut all_children_available = true;
            for child in node.children() {
                if let Some(child_expr) = self.extract_from_eclass(egraph, *child, memo, visiting) {
                    child_exprs.insert(*child, child_expr);
                } else {
                    all_children_available = false;
                    break;
                }
            }
            if !all_children_available {
                continue;
            }

            let expr = node.clone().join_recexprs(|id| child_exprs[&id].clone());
            if contains_z3_model_value(&expr) {
                continue;
            }

            let cost = self.cost_of(&expr);
            let rendered = expr.to_string();
            let should_replace = best.as_ref().is_none_or(|(best_cost, best_rendered, _)| {
                (cost, rendered.as_str()) < (*best_cost, best_rendered.as_str())
            });
            if should_replace {
                best = Some((cost, rendered, expr));
            }
        }

        visiting.remove(&eclass);
        let result = best.map(|(_, _, expr)| expr);
        memo.insert(eclass, result.clone());
        result
    }
}

#[cfg(test)]
mod tests {
    use super::{
        compare_terms_with_cost, compare_terms_with_history, deindex_abstract_term,
        ArrayTermExtractor,
    };
    use crate::{
        cost_functions::YardbirdCostFunction,
        theories::array::array_axioms::{ArrayExpr, ArrayLanguage},
        training::canonical_term_hash,
    };
    use rustc_hash::FxHashMap;
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
            FxHashMap::default(),
            0,
        );

        assert_eq!(extractor.extract(&egraph, b_id).to_string(), "a");
    }

    #[test]
    fn history_penalty_preserves_best_term_until_reuse_outweighs_cost_gap() {
        let a: ArrayExpr = "a".parse().unwrap();
        let b: ArrayExpr = "b".parse().unwrap();
        let mut selection_counts = FxHashMap::default();
        selection_counts.insert(canonical_term_hash(&a), 1);

        assert!(compare_terms_with_history((&a, 0), (&b, 1), &selection_counts, 0).is_lt());

        selection_counts.insert(canonical_term_hash(&a), 2);
        assert!(compare_terms_with_history((&a, 0), (&b, 1), &selection_counts, 0).is_gt());
    }

    #[test]
    fn extractor_uses_history_to_skip_overused_equal_cost_term() {
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        let a: ArrayExpr = "a".parse().unwrap();
        let b: ArrayExpr = "b".parse().unwrap();
        let a_id = egraph.add_expr(&a);
        let b_id = egraph.add_expr(&b);
        egraph.union(a_id, b_id);
        egraph.rebuild();

        let mut selection_counts = FxHashMap::default();
        selection_counts.insert(canonical_term_hash(&a), 1);

        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCostTerms {
                terms: vec![a.clone(), b.clone()],
            },
            0,
            selection_counts,
            0,
        );

        assert_eq!(extractor.extract(&egraph, a_id).to_string(), "b");
    }

    #[test]
    fn extractor_fallback_skips_z3_model_value_symbols() {
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        let model_value: ArrayExpr = "Array_Int_Int!val!8".parse().unwrap();
        let symbolic_array: ArrayExpr = "a".parse().unwrap();
        let model_id = egraph.add_expr(&model_value);
        let symbolic_id = egraph.add_expr(&symbolic_array);
        egraph.union(model_id, symbolic_id);
        egraph.rebuild();

        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCostTerms { terms: vec![] },
            0,
            FxHashMap::default(),
            0,
        );

        assert_eq!(extractor.extract(&egraph, model_id).to_string(), "a");
    }

    #[test]
    fn ranked_fallback_candidates_skip_z3_model_value_symbols() {
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        let model_value: ArrayExpr = "Array_Int_Int!val!8".parse().unwrap();
        let symbolic_array: ArrayExpr = "a".parse().unwrap();
        let model_id = egraph.add_expr(&model_value);
        let symbolic_id = egraph.add_expr(&symbolic_array);
        egraph.union(model_id, symbolic_id);
        egraph.rebuild();

        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCostTerms { terms: vec![] },
            0,
            FxHashMap::default(),
            0,
        );

        let candidates = extractor.ranked_candidates(&egraph, model_id);

        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].0.to_string(), "a");
    }
}
