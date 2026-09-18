//! Array-specific candidate observations for auxiliary synthesis.
use crate::{
    auxiliary_synthesis::ArrayConflictRecord,
    rule_matching::{candidate::InstantiationCandidate, rule::QuantifiedRuleCategory},
    terms::language::expr_to_term,
};

pub(crate) fn capture_conflict(
    candidate: &mut InstantiationCandidate,
    ordinal: usize,
    depth: u16,
    refinement_step: u32,
    decision_keys: Vec<String>,
) {
    if candidate.rule.category() == QuantifiedRuleCategory::ArrayAxiom {
        candidate.conflict = Some(ArrayConflictRecord::new(
            ordinal,
            candidate.provenance.abstract_instantiation_id().to_string(),
            candidate.rule.name(),
            candidate.expression.clone(),
            expr_to_term(candidate.expression.clone()),
            depth,
            refinement_step,
            candidate.cost,
            decision_keys,
        ));
    }
}
