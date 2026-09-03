pub mod candidate;
mod conditional_history;
pub mod config;
pub mod conflict;
pub mod locality;
mod predicate_selector;
pub mod spec;
pub mod trigger;

pub use candidate::{AuxiliaryCaptureTarget, AuxiliarySynthesisCandidate};
pub use conditional_history::ConditionalHistory;
pub use config::{AuxSynthesisConfig, GuardPolicy, SynthesisTrigger};
pub use conflict::ArrayConflictRecord;
pub use locality::FrameSpan;
pub use predicate_selector::InterpolantGuardSelectionRecord;
pub(crate) use predicate_selector::{
    predicate_ast_size, predicate_supports_structural_cost, select_interpolant_guard, Occurrence,
};
pub use spec::{
    term_contains_auxiliary_symbol, AuxiliaryRecord, AuxiliarySpec, HistoryCaptureMode,
    HistorySpec, NonMonotonicityCheckRecord, NonMonotonicityStatus, ProphecySpec,
};
pub use trigger::{AuxTriggerState, TriggerDecision};
