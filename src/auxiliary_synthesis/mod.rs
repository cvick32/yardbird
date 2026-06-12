pub mod config;
pub mod conflict;
pub mod locality;
pub mod spec;
pub mod trigger;

pub use config::{AuxSynthesisConfig, GuardPolicy, SynthesisTrigger};
pub use conflict::{ArrayConflictRecord, ConflictClassification};
pub use locality::FrameSpan;
pub use spec::{
    term_contains_auxiliary_symbol, AuxiliaryRecord, AuxiliarySpec, HistorySpec,
    NonMonotonicityCheckRecord, NonMonotonicityStatus, ProphecySpec,
};
pub use trigger::{AuxTriggerState, TriggerDecision};
