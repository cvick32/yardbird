//! Shared context and exact proposal handling for guided instantiation policies.
//!
//! Providers own prompts, transport, response decoding, and retry scheduling.
//! This module captures the common information and resolves proposals against
//! that vocabulary. Validation checks installability, novelty, and a known-false
//! whole formula. Selection and installation still belong to their existing owners.
//!
//! An adapter captures `InstantiationSnapshot` with the original VMT source,
//! serializes `state()` into its request, and decodes answers into an
//! `InstantiationProposal`. It calls `resolve()` followed by `validate()` using
//! the same live solver model, then returns accepted instances to discovery.
//! Reuse the snapshot across retries; recapture after the solver model changes.
//! The initial shared vocabulary supports Int-indexed, Int-valued arrays only.
mod snapshot;
#[cfg(test)]
mod tests;
mod validation;

pub(crate) use snapshot::{InstantiationProposal, InstantiationSnapshot};
pub(crate) use validation::validate;
