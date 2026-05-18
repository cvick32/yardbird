use serde::{Deserialize, Serialize};
use smt2parser::concrete::Term;

use crate::{auxiliary_synthesis::FrameSpan, theories::array::array_axioms::ArrayExpr};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ConflictClassification {
    Regular,
    ConstOrHighCost,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArrayConflictRecord {
    pub conflict_id: String,
    pub axiom_name: String,
    #[serde(skip)]
    pub abstract_expr: ArrayExpr,
    pub term: Term,
    pub term_hash: String,
    pub depth: u16,
    pub refinement_step: u32,
    pub frame_span: FrameSpan,
    pub is_non_local: bool,
    pub cost: u32,
    pub classification: ConflictClassification,
    pub decision_keys: Vec<String>,
}

impl ArrayConflictRecord {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        ordinal: usize,
        axiom_name: impl Into<String>,
        abstract_expr: ArrayExpr,
        term: Term,
        depth: u16,
        refinement_step: u32,
        cost: u32,
        classification: ConflictClassification,
        decision_keys: Vec<String>,
    ) -> Self {
        let axiom_name = axiom_name.into();
        let term_hash = crate::training::canonical_term_hash(&abstract_expr);
        let frame_span = FrameSpan::from_term(&term);
        let is_non_local = frame_span.is_non_local();
        Self {
            conflict_id: format!("conflict-{depth}-{refinement_step}-{ordinal}"),
            axiom_name,
            abstract_expr,
            term,
            term_hash,
            depth,
            refinement_step,
            frame_span,
            is_non_local,
            cost,
            classification,
            decision_keys,
        }
    }
}
