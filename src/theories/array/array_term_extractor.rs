use std::{cell::RefCell, collections::HashMap, rc::Rc, time::Instant};

use egg::Language;
use rustc_hash::{FxHashMap, FxHashSet};
use smt2parser::vmt::{ReadsAndWrites, VARIABLE_FRAME_DELIMITER};

use crate::{
    cost_functions::{CandidateChoice, CandidateChoiceContext, YardbirdCostFunction},
    problem_context::ArrayCandidateCatalog,
    profiling::ArrayProfilingCollector,
    theories::array::{
        array_axioms::{translate_term, ArrayExpr, ArrayLanguage},
        array_conflict_scheduler::preprocess_array_expr,
        candidate_scope::CandidateScope,
    },
    training::{
        canonical_term_hash, AbstractInstantiationRecord, CandidateRecord, DecisionRecord,
        TermFeatures,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateOrigin {
    SourceGrounded,
    Derived,
}

pub struct ArrayTermExtractorOptions {
    pub candidate_catalog: ArrayCandidateCatalog,
    pub candidate_scope: CandidateScope,
    pub refinement_step: u32,
    pub selection_counts: FxHashMap<String, u32>,
    pub depth: u16,
    pub profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

type RankedTerm = (ArrayExpr, u32);
type CandidatePoolRef<'a> = (&'a Vec<RankedTerm>, CandidateOrigin);
type MatchingWriteCacheKey = (String, String, String, egg::Id, egg::Id);
type WriteCandidateIndex = FxHashMap<String, Vec<(ArrayExpr, ArrayExpr)>>;

fn index_write_candidates(reads_and_writes: &ReadsAndWrites) -> WriteCandidateIndex {
    let mut index = WriteCandidateIndex::default();
    for (raw_array, raw_index, raw_value) in &reads_and_writes.writes_to {
        let Ok(array) = preprocess_array_expr(raw_array).parse::<ArrayExpr>() else {
            continue;
        };
        let Ok(write_index) = preprocess_array_expr(raw_index).parse::<ArrayExpr>() else {
            continue;
        };
        let Ok(write_value) = preprocess_array_expr(raw_value).parse::<ArrayExpr>() else {
            continue;
        };
        index
            .entry(array.to_string())
            .or_default()
            .push((write_index, write_value));
    }
    for candidates in index.values_mut() {
        candidates.sort_by(|left, right| {
            left.0
                .to_string()
                .cmp(&right.0.to_string())
                .then_with(|| left.1.to_string().cmp(&right.1.to_string()))
        });
        candidates.dedup();
    }
    index
}

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

#[cfg(test)]
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
    source_term_map: HashMap<egg::Id, Vec<RankedTerm>>,
    all_term_map: HashMap<egg::Id, Vec<RankedTerm>>,
    source_write_terms: FxHashSet<String>,
    cost_function: CF,
    refinement_step: u32,
    source_write_candidates: WriteCandidateIndex,
    all_write_candidates: WriteCandidateIndex,
    candidate_scope: CandidateScope,
    property_terms: FxHashSet<String>,
    transition_terms: FxHashSet<String>,
    selection_counts: FxHashMap<String, u32>,
    depth: u16,
    profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
    fallback_term_map: RefCell<Option<FxHashMap<egg::Id, ArrayExpr>>>,
    matching_write_cache: RefCell<FxHashMap<MatchingWriteCacheKey, Option<(ArrayExpr, ArrayExpr)>>>,
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
        options: ArrayTermExtractorOptions,
    ) -> Self
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let ArrayTermExtractorOptions {
            candidate_catalog,
            candidate_scope,
            refinement_step,
            selection_counts,
            depth,
            profiling,
        } = options;
        let mut source_term_map: HashMap<egg::Id, Vec<_>> = HashMap::new();
        let mut all_term_map: HashMap<egg::Id, Vec<_>> = HashMap::new();
        let mut source_terms = FxHashSet::default();
        let mut source_write_terms = FxHashSet::default();

        if candidate_scope.tracks_provenance() {
            // The context catalog, not the cost function, is authoritative for
            // whether a term came from the original problem.
            for raw_term in &candidate_catalog.source_grounded.terms {
                let Some(term) = raw_term.parse().ok().and_then(translate_term) else {
                    continue;
                };
                if contains_z3_model_value(&term) {
                    continue;
                }
                source_terms.insert(term.to_string());
                if matches!(term.as_ref().last(), Some(ArrayLanguage::WriteTyped(_))) {
                    source_write_terms.insert(term.to_string());
                }
                let Some(expr) = egraph.lookup_expr(&term) else {
                    continue;
                };
                let cost = self_cost(
                    &mut cost_function,
                    &profiling,
                    "precompute_source_term_map",
                    &term,
                );
                insert_candidate(&mut source_term_map, expr, term, cost);
            }
        }

        // Cost functions can cheaply supply parsed and synthesized terms. Preserve
        // their provenance by checking membership in the source catalog.
        for term in cost_function.get_parsed_terms() {
            if contains_z3_model_value(&term) {
                continue;
            }
            let is_source_grounded = source_terms.contains(&term.to_string());
            let Some(expr) = egraph.lookup_expr(&term) else {
                continue;
            };
            let cost = self_cost(
                &mut cost_function,
                &profiling,
                "precompute_cost_function_term_map",
                &term,
            );
            if candidate_scope.allows_derived() {
                insert_candidate(&mut all_term_map, expr, term.clone(), cost);
            }
            if is_source_grounded {
                insert_candidate(&mut source_term_map, expr, term, cost);
            }
        }

        // Pre-sort all term vectors by cost for faster extraction.
        for terms in source_term_map.values_mut() {
            terms.sort_by(|(left_term, left_cost), (right_term, right_cost)| {
                compare_terms_with_cost((left_term, *left_cost), (right_term, *right_cost))
            });
        }
        if candidate_scope.allows_derived() {
            for terms in all_term_map.values_mut() {
                terms.sort_by(|(left_term, left_cost), (right_term, right_cost)| {
                    compare_terms_with_cost((left_term, *left_cost), (right_term, *right_cost))
                });
            }
        }

        let property_terms = cost_function.get_property_terms().into_iter().collect();
        let transition_terms = cost_function.get_transition_terms().into_iter().collect();
        let all_reads_and_writes = cost_function.get_reads_and_writes();
        let source_write_candidates =
            index_write_candidates(&candidate_catalog.source_grounded.reads_and_writes);
        let all_write_candidates = index_write_candidates(&all_reads_and_writes);

        Self {
            source_term_map,
            all_term_map,
            source_write_terms,
            cost_function,
            refinement_step,
            source_write_candidates,
            all_write_candidates,
            candidate_scope,
            property_terms,
            transition_terms,
            selection_counts,
            depth,
            profiling,
            fallback_term_map: RefCell::new(None),
            matching_write_cache: RefCell::new(FxHashMap::default()),
        }
    }

    pub(crate) fn cached_matching_write(
        &self,
        array: &ArrayExpr,
        index_sort: &str,
        value_sort: &str,
        index_eclass: egg::Id,
        value_eclass: egg::Id,
    ) -> Option<Option<(ArrayExpr, ArrayExpr)>> {
        self.matching_write_cache
            .borrow()
            .get(&(
                array.to_string(),
                index_sort.to_string(),
                value_sort.to_string(),
                index_eclass,
                value_eclass,
            ))
            .cloned()
    }

    pub(crate) fn cache_matching_write(
        &self,
        array: &ArrayExpr,
        index_sort: &str,
        value_sort: &str,
        index_eclass: egg::Id,
        value_eclass: egg::Id,
        result: Option<(ArrayExpr, ArrayExpr)>,
    ) {
        self.matching_write_cache.borrow_mut().insert(
            (
                array.to_string(),
                index_sort.to_string(),
                value_sort.to_string(),
                index_eclass,
                value_eclass,
            ),
            result,
        );
    }

    pub(crate) fn source_write_candidates(&self, array: &ArrayExpr) -> &[(ArrayExpr, ArrayExpr)] {
        self.source_write_candidates
            .get(&array.to_string())
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub(crate) fn all_write_candidates(&self, array: &ArrayExpr) -> &[(ArrayExpr, ArrayExpr)] {
        self.all_write_candidates
            .get(&array.to_string())
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub fn ranked_candidates<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
    ) -> Vec<(ArrayExpr, i32)>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        if let Some(terms) = self.candidates_for_eclass(egraph, eclass) {
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
                let cost = self.cost_of_at("ranked_candidates_fallback", &expr) as i32;
                vec![(expr, cost)]
            })
            .unwrap_or_default()
    }

    pub fn candidate_origin<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
        term: &ArrayExpr,
    ) -> CandidateOrigin
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let eclass = egraph.find(eclass);
        if self
            .source_term_map
            .get(&eclass)
            .is_some_and(|terms| terms.iter().any(|(candidate, _)| candidate == term))
        {
            CandidateOrigin::SourceGrounded
        } else {
            CandidateOrigin::Derived
        }
    }

    pub fn requires_source_grounded_candidates(&self) -> bool {
        self.candidate_scope.requires_source_grounded()
    }

    pub fn prefers_source_on_cost_tie(&self) -> bool {
        self.candidate_scope.prefers_source_on_cost_tie()
    }

    /// A source-only instantiation may choose model-equivalent representatives
    /// for scalar slots, but its array update must remain one exact source site.
    pub fn is_source_write(&self, expr: &ArrayExpr) -> bool {
        self.source_write_terms.contains(&expr.to_string())
    }

    pub fn explores_all_matches(&self) -> bool {
        self.candidate_scope.explores_all_matches()
    }

    pub fn cost_of(&self, expr: &ArrayExpr) -> u32 {
        self.cost_of_at("extractor_cost_of", expr)
    }

    pub fn cost_of_at(&self, site: &'static str, expr: &ArrayExpr) -> u32 {
        let mut cost_fn = self.cost_function.clone();
        if let Some(profiling) = &self.profiling {
            profiling
                .borrow_mut()
                .record_cost(site, expr.as_ref().len(), || cost_fn.cost_rec(expr))
        } else {
            cost_fn.cost_rec(expr)
        }
    }

    pub fn decision_record<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
        axiom_name: &str,
        slot_index: u32,
        chosen_term: &ArrayExpr,
        decision_key: String,
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
                term_hash: chosen_hash,
                is_constant: features.is_constant,
                is_variable: features.is_variable,
                in_property_vocab: features.in_property_vocab,
                in_transition_vocab: features.in_transition_vocab,
                frame_index: features.frame_index,
                ast_size: features.ast_size,
                current_cost: self.cost_of_at("decision_record_append_chosen", chosen_term) as i32,
                was_chosen: true,
            });
        }

        DecisionRecord {
            decision_key,
            bmc_depth: self.depth,
            axiom_name: axiom_name.to_string(),
            slot_index,
            candidates,
        }
    }

    pub fn decision_key(&self, axiom_name: &str, slot_index: u32, eclass: egg::Id) -> String {
        format!(
            "{}:{}:{}:{}:{}",
            axiom_name, self.depth, self.refinement_step, slot_index, eclass
        )
    }

    pub fn abstract_instantiation_record(
        &self,
        axiom_name: &str,
        instantiation: &ArrayExpr,
        decision_keys: Vec<String>,
        substitution: &[(String, smt2parser::concrete::Term)],
    ) -> AbstractInstantiationRecord {
        let abstract_term = deindex_abstract_term(instantiation);
        let term_hash = canonical_term_hash(instantiation);
        let substitution = substitution
            .iter()
            .map(
                |(variable, term)| crate::instantiation_provenance::InstantiationSubstitution {
                    variable: variable.clone(),
                    term: term.to_string(),
                },
            )
            .collect::<Vec<_>>();
        let substitution_key =
            serde_json::to_string(&substitution).expect("substitution should serialize");
        let substitution_hash = crate::training::canonical_term_hash_from_string(&substitution_key);
        AbstractInstantiationRecord {
            abstract_instantiation_id: format!(
                "{}:{}:{}:{}:{}",
                axiom_name, self.depth, self.refinement_step, term_hash, substitution_hash
            ),
            term: abstract_term.to_string(),
            term_hash,
            axiom_name: axiom_name.to_string(),
            bmc_depth: self.depth,
            refinement_step: self.refinement_step,
            decision_keys,
            substitution,
            was_selected: true,
            indexed_assertions_attempted: 0,
            indexed_assertions_added: 0,
            indexed_assertions_deduplicated: 0,
            helper_assertions_attempted: 0,
            helper_assertions_added: 0,
            helper_assertions_deduplicated: 0,
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
        let ml_start = Instant::now();
        let chosen_index = self
            .cost_function
            .choose_candidate_with_ml(&context, &choices)?;
        if let Some(profiling) = &self.profiling {
            profiling
                .borrow_mut()
                .record_timing("ml_choice_total", ml_start.elapsed());
        }
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

    fn choose_with_history<'a, N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
        valid_terms: Vec<&'a (ArrayExpr, u32)>,
        baseline_use_count: u32,
    ) -> Option<(&'a ArrayExpr, u32)>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        valid_terms
            .into_iter()
            .min_by(|(left_term, left_cost), (right_term, right_cost)| {
                let left_penalty = prior_use_count(&self.selection_counts, left_term)
                    .saturating_sub(baseline_use_count);
                let right_penalty = prior_use_count(&self.selection_counts, right_term)
                    .saturating_sub(baseline_use_count);
                left_cost
                    .saturating_add(left_penalty)
                    .cmp(&right_cost.saturating_add(right_penalty))
                    .then_with(|| {
                        if self.prefers_source_on_cost_tie() {
                            let left_derived = self.candidate_origin(egraph, eclass, left_term)
                                == CandidateOrigin::Derived;
                            let right_derived = self.candidate_origin(egraph, eclass, right_term)
                                == CandidateOrigin::Derived;
                            left_derived.cmp(&right_derived)
                        } else {
                            std::cmp::Ordering::Equal
                        }
                    })
                    .then_with(|| {
                        compare_terms_with_cost((left_term, *left_cost), (right_term, *right_cost))
                    })
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
        self.extract_for_decision_with_origin(egraph, eclass, axiom_name, slot_index)
            .0
    }

    pub fn extract_for_decision_with_origin<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
        axiom_name: &str,
        slot_index: u32,
    ) -> (egg::RecExpr<ArrayLanguage>, CandidateOrigin)
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        if let Some((terms, _)) = self.candidates_with_origin(egraph, eclass) {
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
                let origin = self.candidate_origin(egraph, eclass, term);
                return (term.clone(), origin);
            }

            if let Some((term, cost)) =
                self.choose_with_history(egraph, eclass, valid_terms, baseline_use_count)
            {
                let prior_uses = prior_use_count(&self.selection_counts, term);
                log::debug!(
                    "history-aware term: {eclass} -> {} base_cost={} prior_uses={} penalty={}",
                    term,
                    cost,
                    prior_uses,
                    prior_uses.saturating_sub(baseline_use_count)
                );
                let origin = self.candidate_origin(egraph, eclass, term);
                return (term.clone(), origin);
            }
        }

        (
            self.extract_from_egraph(egraph, eclass).unwrap_or_else(|| {
                panic!("No non-Z3-model representative available for e-class {eclass}")
            }),
            CandidateOrigin::Derived,
        )
    }

    fn candidates_for_eclass<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
    ) -> Option<&Vec<(ArrayExpr, CF::Cost)>>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        self.candidates_with_origin(egraph, eclass)
            .map(|(terms, _)| terms)
    }

    fn candidates_with_origin<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
    ) -> Option<CandidatePoolRef<'_>>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let eclass = egraph.find(eclass);
        match self.candidate_scope {
            CandidateScope::SourceGroundedOnly => self
                .source_term_map
                .get(&eclass)
                .map(|terms| (terms, CandidateOrigin::SourceGrounded)),
            CandidateScope::AllCandidates => self.all_term_map.get(&eclass).map(|terms| {
                let origin = if self.source_term_map.contains_key(&eclass) {
                    CandidateOrigin::SourceGrounded
                } else {
                    CandidateOrigin::Derived
                };
                (terms, origin)
            }),
        }
    }

    fn extract_from_egraph<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        eclass: egg::Id,
    ) -> Option<ArrayExpr>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        if self.fallback_term_map.borrow().is_none() {
            let computed = self.compute_fallback_terms(egraph);
            *self.fallback_term_map.borrow_mut() = Some(computed);
        }

        self.fallback_term_map
            .borrow()
            .as_ref()
            .and_then(|terms| terms.get(&egraph.find(eclass)).cloned())
    }

    fn compute_fallback_terms<N>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
    ) -> FxHashMap<egg::Id, ArrayExpr>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let mut best_by_eclass: FxHashMap<egg::Id, (u32, String, ArrayExpr)> = FxHashMap::default();

        loop {
            let mut changed = false;

            for class in egraph.classes() {
                let class_id = egraph.find(class.id);
                let existing = best_by_eclass.get(&class_id).cloned();
                let mut best = existing.clone();

                for node in &class.nodes {
                    if is_z3_model_value_node(node) {
                        continue;
                    }

                    let mut child_exprs = FxHashMap::default();
                    let mut all_children_available = true;
                    for child in node.children() {
                        let child_class = egraph.find(*child);
                        if let Some((_, _, child_expr)) = best_by_eclass.get(&child_class) {
                            child_exprs.insert(*child, child_expr.clone());
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

                    let cost = self.cost_of_at("fallback_extract_best", &expr);
                    let rendered = expr.to_string();
                    let should_replace =
                        best.as_ref().is_none_or(|(best_cost, best_rendered, _)| {
                            (cost, rendered.as_str()) < (*best_cost, best_rendered.as_str())
                        });
                    if should_replace {
                        best = Some((cost, rendered, expr));
                    }
                }

                let improved = match (&existing, &best) {
                    (None, Some(_)) => true,
                    (Some((old_cost, old_rendered, _)), Some((cost, rendered, _))) => {
                        (cost, rendered) < (old_cost, old_rendered)
                    }
                    _ => false,
                };
                if improved {
                    best_by_eclass.insert(class_id, best.unwrap());
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        best_by_eclass
            .into_iter()
            .map(|(eclass, (_, _, expr))| (eclass, expr))
            .collect()
    }
}

fn self_cost<CF>(
    cost_function: &mut CF,
    profiling: &Option<Rc<RefCell<ArrayProfilingCollector>>>,
    site: &'static str,
    term: &ArrayExpr,
) -> u32
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    if let Some(profiling) = profiling {
        profiling
            .borrow_mut()
            .record_cost(site, term.as_ref().len(), || cost_function.cost_rec(term))
    } else {
        cost_function.cost_rec(term)
    }
}

fn insert_candidate<C: Copy + Ord>(
    term_map: &mut HashMap<egg::Id, Vec<(ArrayExpr, C)>>,
    eclass: egg::Id,
    term: ArrayExpr,
    cost: C,
) {
    let candidates = term_map.entry(eclass).or_default();
    if !candidates.iter().any(|(existing, _)| existing == &term) {
        candidates.push((term, cost));
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::Cell, rc::Rc};

    use super::{
        compare_terms_with_cost, compare_terms_with_history, deindex_abstract_term,
        ArrayTermExtractor, ArrayTermExtractorOptions, CandidateOrigin,
    };
    use crate::theories::array::candidate_scope::CandidateScope;
    use crate::{
        cost_functions::YardbirdCostFunction,
        problem_context::{ArrayCandidateCatalog, ArrayCandidatePool},
        theories::array::array_axioms::{ArrayExpr, ArrayLanguage},
        training::canonical_term_hash,
    };
    use rustc_hash::FxHashMap;
    use smt2parser::vmt::ReadsAndWrites;

    #[derive(Clone)]
    struct ZeroCostTerms {
        terms: Vec<ArrayExpr>,
    }

    #[derive(Clone)]
    struct CountingCost {
        calls: Rc<Cell<u32>>,
    }

    fn options(
        candidate_catalog: ArrayCandidateCatalog,
        candidate_scope: CandidateScope,
        selection_counts: FxHashMap<String, u32>,
    ) -> ArrayTermExtractorOptions {
        ArrayTermExtractorOptions {
            candidate_catalog,
            candidate_scope,
            refinement_step: 0,
            selection_counts,
            depth: 0,
            profiling: None,
        }
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

    impl egg::CostFunction<ArrayLanguage> for CountingCost {
        type Cost = u32;

        fn cost<C>(&mut self, _enode: &ArrayLanguage, _costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            self.calls.set(self.calls.get() + 1);
            0
        }
    }

    impl YardbirdCostFunction<ArrayLanguage> for CountingCost {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
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
            options(
                ArrayCandidateCatalog::default(),
                CandidateScope::AllCandidates,
                FxHashMap::default(),
            ),
        );

        assert_eq!(extractor.extract(&egraph, b_id).to_string(), "a");
    }

    #[test]
    fn extractor_does_not_score_candidates_absent_from_the_partial_egraph() {
        let egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        let calls = Rc::new(Cell::new(0));

        let _ = ArrayTermExtractor::new(
            &egraph,
            CountingCost {
                calls: calls.clone(),
            },
            options(
                ArrayCandidateCatalog {
                    source_grounded: ArrayCandidatePool {
                        terms: vec!["not_in_the_cone".to_string()],
                        ..ArrayCandidatePool::default()
                    },
                    derived: ArrayCandidatePool::default(),
                },
                CandidateScope::SourceGroundedOnly,
                FxHashMap::default(),
            ),
        );

        assert_eq!(calls.get(), 0);
    }

    #[test]
    fn fallback_extraction_is_computed_once_per_egraph() {
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        let expression: ArrayExpr = "(+ a b)".parse().unwrap();
        let eclass = egraph.add_expr(&expression);
        egraph.rebuild();
        let calls = Rc::new(Cell::new(0));
        let extractor = ArrayTermExtractor::new(
            &egraph,
            CountingCost {
                calls: calls.clone(),
            },
            options(
                ArrayCandidateCatalog::default(),
                CandidateScope::AllCandidates,
                FxHashMap::default(),
            ),
        );

        assert_eq!(extractor.extract(&egraph, eclass), expression);
        let calls_after_first_extraction = calls.get();
        assert!(calls_after_first_extraction > 0);
        assert_eq!(extractor.extract(&egraph, eclass), expression);
        assert_eq!(calls.get(), calls_after_first_extraction);
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
            options(
                ArrayCandidateCatalog::default(),
                CandidateScope::AllCandidates,
                selection_counts,
            ),
        );

        assert_eq!(extractor.extract(&egraph, a_id).to_string(), "b");
    }

    #[test]
    fn source_grounded_candidate_wins_before_derived_candidate() {
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        let derived: ArrayExpr = "a".parse().unwrap();
        let source: ArrayExpr = "z".parse().unwrap();
        let derived_id = egraph.add_expr(&derived);
        let source_id = egraph.add_expr(&source);
        egraph.union(derived_id, source_id);
        egraph.rebuild();

        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCostTerms { terms: vec![] },
            options(
                ArrayCandidateCatalog {
                    source_grounded: ArrayCandidatePool {
                        terms: vec!["z".to_string()],
                        ..ArrayCandidatePool::default()
                    },
                    derived: ArrayCandidatePool {
                        terms: vec!["a".to_string()],
                        ..ArrayCandidatePool::default()
                    },
                },
                CandidateScope::SourceGroundedOnly,
                FxHashMap::default(),
            ),
        );

        let (chosen, origin) =
            extractor.extract_for_decision_with_origin(&egraph, source_id, "test", 0);
        assert_eq!(chosen.to_string(), "z");
        assert_eq!(origin, CandidateOrigin::SourceGrounded);
    }

    #[test]
    fn source_only_scope_classifies_egraph_fallback_as_derived() {
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        let value: ArrayExpr = "137".parse().unwrap();
        let value_id = egraph.add_expr(&value);
        egraph.rebuild();

        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCostTerms { terms: vec![] },
            options(
                ArrayCandidateCatalog::default(),
                CandidateScope::SourceGroundedOnly,
                FxHashMap::default(),
            ),
        );

        let (_, origin) = extractor.extract_for_decision_with_origin(&egraph, value_id, "test", 0);
        assert_eq!(origin, CandidateOrigin::Derived);
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
            options(
                ArrayCandidateCatalog::default(),
                CandidateScope::AllCandidates,
                FxHashMap::default(),
            ),
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
            options(
                ArrayCandidateCatalog::default(),
                CandidateScope::AllCandidates,
                FxHashMap::default(),
            ),
        );

        let candidates = extractor.ranked_candidates(&egraph, model_id);

        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].0.to_string(), "a");
    }
}
