use crate::{
    auxiliary_synthesis::ArrayConflictRecord,
    instantiation_provenance::InstantiationProvenance,
    quantified_rule::QuantifiedRule,
    theories::array::array_axioms::ArrayExpr,
    training::{AbstractInstantiationRecord, DecisionRecord},
};

/// One term-selection decision retained beside its complete instantiation.
#[derive(Clone, Debug)]
pub(crate) struct SelectionHistoryDecision {
    pub(crate) decision_key: String,
    pub(crate) chosen_term_hash: String,
}

/// One complete quantified-rule candidate and its correlated artifacts.
#[derive(Clone, Debug)]
pub struct InstantiationCandidate {
    pub rule: QuantifiedRule,
    pub expression: ArrayExpr,
    pub cost: u32,
    pub provenance: InstantiationProvenance,
    pub selected: bool,
    pub decisions: Vec<DecisionRecord>,
    pub(crate) selection_history: Vec<SelectionHistoryDecision>,
    pub abstract_instantiation: Option<AbstractInstantiationRecord>,
    pub conflict: Option<ArrayConflictRecord>,
}

/// Candidates generated during one read-only array-rule search.
#[derive(Default)]
pub struct InstantiationBatch {
    pub candidates: Vec<InstantiationCandidate>,
}

impl InstantiationBatch {
    pub fn selected(&self) -> impl Iterator<Item = &InstantiationCandidate> {
        self.candidates
            .iter()
            .filter(|candidate| candidate.selected)
    }

    pub(crate) fn selected_mut(&mut self) -> impl Iterator<Item = &mut InstantiationCandidate> {
        self.candidates
            .iter_mut()
            .filter(|candidate| candidate.selected)
    }

    pub fn into_selected(self) -> impl Iterator<Item = InstantiationCandidate> {
        self.candidates
            .into_iter()
            .filter(|candidate| candidate.selected)
    }
}
