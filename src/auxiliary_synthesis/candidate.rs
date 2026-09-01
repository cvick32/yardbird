use smt2parser::concrete::{Sort, Term};

use crate::auxiliary_synthesis::{ArrayConflictRecord, GuardPolicy, SynthesisTrigger};

/// A scalar state variable selected as the value a history variable should
/// capture from the concrete counterexample epoch.
#[derive(Clone, Debug)]
pub struct AuxiliaryCaptureTarget {
    pub current_name: String,
    pub next_name: String,
    pub frame: i64,
    pub sort: Sort,
}

/// A conflict selected by an abstract strategy for synchronous auxiliary
/// synthesis during concrete counterexample validation.
#[derive(Clone, Debug)]
pub struct AuxiliarySynthesisCandidate {
    pub aux_id: String,
    pub conflict: ArrayConflictRecord,
    pub capture_target: AuxiliaryCaptureTarget,
    pub history_name: String,
    pub prophecy_name: String,
    pub localized_axiom: Term,
    pub trigger: SynthesisTrigger,
    pub guard_policy: GuardPolicy,
}

impl AuxiliarySynthesisCandidate {
    pub fn source_conflict_id(&self) -> &str {
        &self.conflict.conflict_id
    }
}
