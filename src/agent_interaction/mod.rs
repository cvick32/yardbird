//! Agent interaction with Yardbird through stdio, native refinement, and batch verification.
mod native;
pub mod one_shot;
pub use native::NativeAgent;
pub(crate) use options::migrate_saved_options;
pub use options::{AgentMode, AgentTrigger};
pub(crate) mod observations;
mod options;
mod protocol;
pub(crate) mod records;
pub use options::AgentOptions;
