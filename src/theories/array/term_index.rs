//! Array write-site indexes and lookup caches used during term extraction.
use crate::{
    policy::term_selection::YardbirdCostFunction,
    rule_matching::extractor::TermExtractor,
    terms::language::{translate_term, TermExpr, TermLanguage},
};
use rustc_hash::{FxHashMap, FxHashSet};
use smt2parser::vmt::ReadsAndWrites;
use std::cell::RefCell;

#[derive(Default)]
pub(crate) struct ArrayTermIndex {
    source_write_terms: FxHashSet<String>,
    source_write_candidates: WriteCandidateIndex,
    all_write_candidates: WriteCandidateIndex,
    matching_write_cache: RefCell<FxHashMap<MatchingWriteCacheKey, Option<(TermExpr, TermExpr)>>>,
}

impl ArrayTermIndex {
    pub(crate) fn admit_source_term(&mut self, term: &TermExpr) {
        if matches!(term.as_ref().last(), Some(TermLanguage::WriteTyped(_))) {
            self.source_write_terms.insert(term.to_string());
        }
    }
    pub(crate) fn index_writes(&mut self, source: &ReadsAndWrites, all: &ReadsAndWrites) {
        self.source_write_candidates = index_write_candidates(source);
        self.all_write_candidates = index_write_candidates(all);
    }
}

type MatchingWriteCacheKey = (String, String, String, egg::Id, egg::Id);
type WriteCandidateIndex = FxHashMap<String, Vec<(TermExpr, TermExpr)>>;

fn index_write_candidates(reads_and_writes: &ReadsAndWrites) -> WriteCandidateIndex {
    let mut index = WriteCandidateIndex::default();
    for (raw_array, raw_index, raw_value) in &reads_and_writes.writes_to {
        // These strings are printed SMT terms, not egg expressions. Use the
        // source-term translation so quoted symbols have identical identities
        // in the write-site index and the model-equivalence e-graph.
        let Some(array) = raw_array.parse().ok().and_then(translate_term) else {
            continue;
        };
        let Some(write_index) = raw_index.parse().ok().and_then(translate_term) else {
            continue;
        };
        let Some(write_value) = raw_value.parse().ok().and_then(translate_term) else {
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

impl<CF: YardbirdCostFunction<TermLanguage>> TermExtractor<CF> {
    pub(crate) fn cached_matching_write(
        &self,
        array: &TermExpr,
        index_sort: &str,
        value_sort: &str,
        index_eclass: egg::Id,
        value_eclass: egg::Id,
    ) -> Option<Option<(TermExpr, TermExpr)>> {
        self.array_terms
            .matching_write_cache
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
        array: &TermExpr,
        index_sort: &str,
        value_sort: &str,
        index_eclass: egg::Id,
        value_eclass: egg::Id,
        result: Option<(TermExpr, TermExpr)>,
    ) {
        self.array_terms.matching_write_cache.borrow_mut().insert(
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

    pub(crate) fn source_write_candidates(&self, array: &TermExpr) -> &[(TermExpr, TermExpr)] {
        self.array_terms
            .source_write_candidates
            .get(&array.to_string())
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub(crate) fn source_candidates_for_eclass<N>(
        &self,
        egraph: &egg::EGraph<TermLanguage, N>,
        eclass: egg::Id,
    ) -> Vec<TermExpr>
    where
        N: egg::Analysis<TermLanguage>,
    {
        let eclass = egraph.find(eclass);
        let mut expressions: Vec<TermExpr> = self
            .source_term_candidates(egraph.find(eclass))
            .map(|candidates| {
                candidates
                    .iter()
                    .map(|(expression, _)| expression.clone())
                    .collect()
            })
            .unwrap_or_default();
        for raw_array in self.array_terms.source_write_candidates.keys() {
            let Ok(array) = raw_array.parse::<TermExpr>() else {
                continue;
            };
            if egraph
                .lookup_expr(&array)
                .is_some_and(|candidate| egraph.find(candidate) == eclass)
            {
                expressions.push(array);
            }
        }
        expressions.sort_by_key(ToString::to_string);
        expressions.dedup();
        expressions
    }

    pub(crate) fn all_write_candidates(&self, array: &TermExpr) -> &[(TermExpr, TermExpr)] {
        self.array_terms
            .all_write_candidates
            .get(&array.to_string())
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    /// A source-only instantiation may choose model-equivalent representatives
    /// for scalar slots, but its array update must remain one exact source site.
    pub fn is_source_write(&self, expr: &TermExpr) -> bool {
        self.array_terms
            .source_write_terms
            .contains(&expr.to_string())
    }
}
