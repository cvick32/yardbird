use serde::{Deserialize, Serialize};
use smt2parser::concrete::Term;

use crate::{auxiliary_synthesis::FrameSpan, theories::array::array_axioms::ArrayExpr};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArrayConflictRecord {
    pub conflict_id: String,
    #[serde(default)]
    pub abstract_instantiation_id: String,
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
    pub decision_keys: Vec<String>,
}

impl ArrayConflictRecord {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        ordinal: usize,
        abstract_instantiation_id: impl Into<String>,
        axiom_name: impl Into<String>,
        abstract_expr: ArrayExpr,
        term: Term,
        depth: u16,
        refinement_step: u32,
        cost: u32,
        decision_keys: Vec<String>,
    ) -> Self {
        let axiom_name = axiom_name.into();
        let term_hash = crate::training::canonical_term_hash(&abstract_expr);
        let frame_span = FrameSpan::from_term(&term);
        let is_non_local = frame_span.is_non_local();
        Self {
            conflict_id: format!("conflict-{depth}-{refinement_step}-{ordinal}"),
            abstract_instantiation_id: abstract_instantiation_id.into(),
            axiom_name,
            abstract_expr,
            term,
            term_hash,
            depth,
            refinement_step,
            frame_span,
            is_non_local,
            cost,
            decision_keys,
        }
    }
}
