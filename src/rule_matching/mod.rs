//! Shared matching, representative extraction, and candidate construction.
pub mod candidate;
pub mod candidate_builder;
pub(crate) mod compiled_rule;
pub mod extractor;
pub(crate) mod grounding;
pub mod provenance;
pub mod rule;
pub mod scope;
pub(crate) mod search;
pub(crate) mod search_context;
