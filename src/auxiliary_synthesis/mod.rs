pub mod config;
pub mod conflict;
pub mod locality;
pub mod trigger;

pub use config::{AuxSynthesisConfig, GuardPolicy, SynthesisTrigger};
pub use conflict::{ArrayConflictRecord, ConflictClassification};
pub use locality::FrameSpan;
pub use trigger::{AuxTriggerState, TriggerDecision};
