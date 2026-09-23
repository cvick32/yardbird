use crate::auxiliary_synthesis::ArrayConflictRecord;
use crate::rule_matching::provenance::InstantiationProvenance;
use crate::rule_matching::rule::{QuantifiedRule, QuantifiedRuleCategory};
use crate::rule_matching::scope::CandidateScope;
use crate::terms::language::{expr_to_term, TermExpr};
use crate::training::{AbstractInstantiationRecord, DecisionRecord};

use rustc_hash::FxHashMap;
use smt2parser::concrete::Term;
use std::{hash::Hash, mem};

/// One term-selection decision retained beside its complete instantiation.
#[derive(Clone, Debug)]
pub(crate) struct SelectionHistoryDecision {
    pub(crate) decision_key: String,
    pub(crate) chosen_term_hash: String,
}

/// The stable unit over which a selection policy chooses one candidate.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum CandidateGroup {
    MatchRoot(egg::Id),
    Rule,
}

/// Whether every binding in a complete instantiation came from source syntax
/// or at least one binding came from a solver/model-derived representative.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InstantiationGrounding {
    SourceGrounded,
    Derived,
}

/// One complete quantified-rule candidate and its metadata
#[derive(Clone, Debug)]
pub struct InstantiationCandidate {
    pub rule: QuantifiedRule,
    pub expression: TermExpr,
    pub cost: u32,
    pub grounding: InstantiationGrounding,
    pub provenance: InstantiationProvenance,
    pub selected: bool,
    pub decisions: Vec<DecisionRecord>,
    pub(crate) selection_history: Vec<SelectionHistoryDecision>,
    pub abstract_instantiation: Option<AbstractInstantiationRecord>,
    pub conflict: Option<ArrayConflictRecord>,
    pub(crate) group: CandidateGroup,
    /// The candidate was retained only after its formula evaluated to false in
    /// the current model, so batch preparation must not evaluate it again.
    pub(crate) model_violation_verified: bool,
}

#[derive(Debug, Default, Eq, PartialEq)]
pub(crate) struct RuleCandidateCounts {
    pub(crate) generated: usize,
    pub(crate) selected: usize,
    pub(crate) rejected_known_or_uninstallable: usize,
}

/// Batch-local outcomes for the strategy's logging and progress checks.
#[derive(Debug, Default)]
pub(crate) struct BatchSummary {
    pub(crate) by_rule: FxHashMap<String, RuleCandidateCounts>,
    pub(crate) rejected_model: usize,
    /// Known, duplicate, or uninstallable candidates.
    pub(crate) rejected_known: usize,
    /// Candidates retained for diagnostics but rejected by the configured
    /// whole-instantiation ranker in this search phase.
    pub(crate) rejected_ranker: usize,
    pub(crate) selected_arrays: usize,
    pub(crate) selected_guards: usize,
    pub(crate) selected_binders: usize,
    pub(crate) conflicts: usize,
}

impl BatchSummary {
    #[cfg(test)]
    pub(crate) fn selected_count(&self) -> usize {
        self.selected_arrays + self.selected_guards + self.selected_binders
    }
}

/// Candidates generated during one theory search pass.
#[derive(Default)]
pub struct InstantiationBatch {
    pub search: crate::rule_matching::search::RuleSearchReport,
    pub candidates: Vec<InstantiationCandidate>,
}

impl InstantiationBatch {
    pub fn selected(&self) -> impl Iterator<Item = &InstantiationCandidate> {
        self.candidates
            .iter()
            .filter(|candidate| candidate.selected)
    }

    pub fn into_selected(self) -> impl Iterator<Item = InstantiationCandidate> {
        self.candidates
            .into_iter()
            .filter(|candidate| candidate.selected)
    }

    pub(crate) fn filter_model(
        &mut self,
        scope: CandidateScope,
        mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
    ) -> anyhow::Result<usize> {
        let before = self.candidates.len();
        let mut eligible = Vec::with_capacity(before);
        let mut evaluations = FxHashMap::<String, String>::default();
        for candidate in mem::take(&mut self.candidates) {
            let requires_model_violation = candidate.rule.category()
                == QuantifiedRuleCategory::TransitionGuard
                || scope.requires_model_violation();
            if !requires_model_violation {
                eligible.push(candidate);
                continue;
            }
            if candidate.model_violation_verified {
                eligible.push(candidate);
                continue;
            }
            let term = expr_to_term(candidate.expression.clone());
            if model_value(&term, &mut evaluate, &mut evaluations)?.trim() == "false" {
                eligible.push(candidate);
            }
        }
        let rejected = before - eligible.len();
        self.candidates = eligible;
        Ok(rejected)
    }
}

pub(crate) fn model_value(
    term: &Term,
    evaluate: &mut impl FnMut(&Term) -> anyhow::Result<String>,
    cache: &mut FxHashMap<String, String>,
) -> anyhow::Result<String> {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return cached_model_value(term, evaluate, cache);
    };
    if qual_identifier.get_name() != "=>" || arguments.len() != 2 {
        return cached_model_value(term, evaluate, cache);
    }

    match cached_model_value(&arguments[0], evaluate, cache)?.trim() {
        "false" => Ok("true".to_string()),
        "true" => cached_model_value(&arguments[1], evaluate, cache),
        _ => cached_model_value(term, evaluate, cache),
    }
}

fn cached_model_value(
    term: &Term,
    evaluate: &mut impl FnMut(&Term) -> anyhow::Result<String>,
    cache: &mut FxHashMap<String, String>,
) -> anyhow::Result<String> {
    let key = term.to_string();
    if let Some(value) = cache.get(&key) {
        return Ok(value.clone());
    }
    let value = evaluate(term)?;
    cache.insert(key, value.clone());
    Ok(value)
}

/// Exact, valid theory instance discovered without representative extraction.
/// Terms retain absolute frames until ordinary installation normalizes them.
#[derive(Clone)]
pub(crate) struct SymbolicInstance {
    pub rule: QuantifiedRule,
    pub term: Term,
    pub bindings: Vec<(String, Term)>,
}
