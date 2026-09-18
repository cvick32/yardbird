//! Shared term representation, matching, grounding and whole-instance selection.
pub mod candidate;
pub mod engine;
pub mod extractor;
pub(crate) mod grounding;
pub mod instantiator;
pub mod language;
pub(crate) mod parser;
pub mod provenance;
pub mod ranker;
pub mod rule;
pub mod scope;
pub(crate) mod search;
