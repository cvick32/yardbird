use egg::Language;
use rustc_hash::FxHashSet;
use smt2parser::vmt::ReadsAndWrites;

use crate::{
    cost_functions::{
        array::ArrayCostFactory, CandidateChoice, CandidateChoiceContext, YardbirdCostFunction,
    },
    problem_context::ProblemContext,
    theories::array::array_axioms::ArrayLanguage,
    training::{
        canonical_term_hash, LogisticRegressionCandidateFeatures, LogisticRegressionModel,
        TermFeatures,
    },
};

/// Standalone logistic-regression cost function for learned term selection.
#[derive(Clone, Debug)]
pub struct LogisticRegression {
    pub current_bmc_depth: u32,
    pub init_and_transition_system_terms: Vec<String>,
    pub property_terms: Vec<String>,
    transition_term_set: FxHashSet<String>,
    property_term_set: FxHashSet<String>,
    pub reads_writes: ReadsAndWrites,
    model: LogisticRegressionModel,
}

impl LogisticRegression {
    pub fn new(
        current_bmc_depth: u32,
        init_and_transition_system_terms: Vec<String>,
        property_terms: Vec<String>,
        reads_writes: ReadsAndWrites,
        model: LogisticRegressionModel,
    ) -> Self {
        let transition_term_set = init_and_transition_system_terms
            .iter()
            .cloned()
            .collect::<FxHashSet<_>>();
        let property_term_set = property_terms.iter().cloned().collect::<FxHashSet<_>>();
        Self {
            current_bmc_depth,
            init_and_transition_system_terms,
            property_terms,
            transition_term_set,
            property_term_set,
            reads_writes,
            model,
        }
    }
}

impl ArrayCostFactory for LogisticRegression {
    type Config = LogisticRegressionModel;

    fn from_context(smt: &dyn ProblemContext, depth: u32, model: &Self::Config) -> Self {
        Self::new(
            depth,
            smt.get_init_and_transition_subterms(),
            smt.get_property_subterms(),
            smt.get_reads_and_writes(),
            model.clone(),
        )
    }
}

impl egg::CostFunction<ArrayLanguage> for LogisticRegression {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        enode.fold(1, |sum, id| sum + costs(id))
    }
}

impl YardbirdCostFunction<ArrayLanguage> for LogisticRegression {
    fn get_string_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms
            .iter()
            .chain(self.property_terms.iter())
            .map(|term| term.as_str().to_string())
            .collect()
    }

    fn get_transition_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms.clone()
    }

    fn get_property_terms(&self) -> Vec<String> {
        self.property_terms.clone()
    }

    fn get_reads_and_writes(&self) -> ReadsAndWrites {
        self.reads_writes.clone()
    }

    fn choose_candidate_with_ml(
        &self,
        context: &CandidateChoiceContext<'_>,
        candidates: &[CandidateChoice<'_>],
    ) -> Option<usize> {
        let mut best: Option<(usize, f64)> = None;
        for (index, candidate) in candidates.iter().enumerate() {
            let term_features = TermFeatures::extract(
                candidate.term,
                &self.property_term_set,
                &self.transition_term_set,
            );
            let features = LogisticRegressionCandidateFeatures {
                axiom_name: context.axiom_name,
                slot_index: context.slot_index,
                is_constant: term_features.is_constant,
                is_variable: term_features.is_variable,
                in_property_vocab: term_features.in_property_vocab,
                in_transition_vocab: term_features.in_transition_vocab,
                frame_index: term_features.frame_index,
                ast_size: term_features.ast_size,
                current_cost: i32::try_from(candidate.current_cost).unwrap_or(i32::MAX),
                bmc_depth: context.bmc_depth,
                cost_rank: candidate.cost_rank,
                cost_rank_frac: candidate.cost_rank_frac,
                candidate_count: candidate.candidate_count,
            };
            let score = self.model.score(&features);
            let should_replace = match best {
                None => true,
                Some((best_index, best_score)) => match score.total_cmp(&best_score) {
                    std::cmp::Ordering::Greater => true,
                    std::cmp::Ordering::Less => false,
                    std::cmp::Ordering::Equal => {
                        compare_candidate_tiebreak(candidate, &candidates[best_index]).is_lt()
                    }
                },
            };
            if should_replace {
                best = Some((index, score));
            }
        }
        best.map(|(index, _)| index)
    }
}

fn compare_candidate_tiebreak(
    left: &CandidateChoice<'_>,
    right: &CandidateChoice<'_>,
) -> std::cmp::Ordering {
    left.current_cost
        .saturating_add(left.prior_use_count)
        .cmp(&right.current_cost.saturating_add(right.prior_use_count))
        .then_with(|| left.cost_rank.cmp(&right.cost_rank))
        .then_with(|| left.term.as_ref().len().cmp(&right.term.as_ref().len()))
        .then_with(|| canonical_term_hash(left.term).cmp(&canonical_term_hash(right.term)))
        .then_with(|| left.term.to_string().cmp(&right.term.to_string()))
}
