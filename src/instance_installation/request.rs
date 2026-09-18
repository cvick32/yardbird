//! Requests, stored instances, and installation outcomes.
use crate::rule_matching::provenance::InstantiationProvenance;
use serde::{Deserialize, Serialize};
use smt2parser::vmt::quantified_instantiator::Instance;

/// A normalized theory instance together with its exact candidate provenance.
#[derive(Clone, Debug)]
pub struct InstantiationRequest {
    pub(crate) inst: Instance,
    pub(crate) provenance: Option<InstantiationProvenance>,
}

impl InstantiationRequest {
    pub fn untracked(inst: Instance) -> Self {
        Self {
            inst,
            provenance: None,
        }
    }

    pub fn provenanced(inst: Instance, provenance: InstantiationProvenance) -> Self {
        Self {
            inst,
            provenance: Some(provenance),
        }
    }
}

#[derive(Clone, Debug)]
pub struct StoredInstantiation {
    pub inst: Instance,
    pub provenance: Option<InstantiationProvenance>,
}

/// Observable outcome of installing one whole theory instantiation.
///
/// An abstract instance may be new while adding no solver-visible assertion
/// because every materialized placement was removed by canonical deduplication.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct InstantiationInstallResult {
    pub abstract_instance_added: bool,
    pub indexed_assertions_attempted: u64,
    pub indexed_assertions_added: u64,
    pub indexed_assertions_deduplicated: u64,
    pub helper_assertions_attempted: u64,
    pub helper_assertions_added: u64,
    pub helper_assertions_deduplicated: u64,
}

impl InstantiationInstallResult {
    pub fn solver_assertions_added(self) -> u64 {
        self.indexed_assertions_added + self.helper_assertions_added
    }
}
