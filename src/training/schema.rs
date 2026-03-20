//! Schema types for training data logging.
//!
//! These types correspond to the database schema defined in the migrations.

use serde::{Deserialize, Serialize};

/// Record for a single instantiation decision point.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecisionRecord {
    /// Stable key for joining decisions to later instantiations within a run
    pub decision_key: String,
    /// BMC depth at which this decision was made
    pub bmc_depth: u16,
    /// Name of the axiom being instantiated (e.g., "write-does-not-overwrite-Int-Int")
    pub axiom_name: String,
    /// Index of the variable slot being instantiated (0-indexed position in pattern)
    pub slot_index: u32,
    /// Candidates considered for this decision
    pub candidates: Vec<CandidateRecord>,
}

/// Record for a single candidate term considered during instantiation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CandidateRecord {
    /// String representation of the term
    pub term: String,
    /// Canonical hash for matching to unsat core
    pub term_hash: String,
    /// Whether the term is a constant (no frame indices)
    pub is_constant: bool,
    /// Whether the term is a simple variable
    pub is_variable: bool,
    /// Whether the term appears in property vocabulary
    pub in_property_vocab: bool,
    /// Whether the term appears in transition/init vocabulary
    pub in_transition_vocab: bool,
    /// Frame index if term is a state variable (None for constants)
    pub frame_index: Option<i32>,
    /// AST size (number of nodes)
    pub ast_size: i32,
    /// Cost assigned by current cost function
    pub current_cost: i32,
    /// Whether this candidate was chosen
    pub was_chosen: bool,
}

impl CandidateRecord {
    /// Create a new CandidateRecord with default features
    pub fn new(term: String, term_hash: String) -> Self {
        CandidateRecord {
            term,
            term_hash,
            is_constant: false,
            is_variable: false,
            in_property_vocab: false,
            in_transition_vocab: false,
            frame_index: None,
            ast_size: 0,
            current_cost: 0,
            was_chosen: false,
        }
    }
}

/// Record for a single original abstract instantiation before BMC unrolling.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AbstractInstantiationRecord {
    /// Stable identifier for this abstract instantiation within a benchmark run
    pub abstract_instantiation_id: String,
    /// String representation of the unindexed instantiation term
    pub term: String,
    /// Canonical hash for matching and deduplication
    pub term_hash: String,
    /// Name of the source axiom / rewrite
    pub axiom_name: String,
    /// BMC depth at which this abstract instantiation was synthesized
    pub bmc_depth: u16,
    /// Refinement step at which this abstract instantiation was synthesized
    pub refinement_step: u32,
    /// Decision keys that were used to build this instantiation
    pub decision_keys: Vec<String>,
    /// Whether any tracked solver assertion derived from this instantiation appeared in the core
    pub in_unsat_core: bool,
}

/// Record for a single indexed instantiation (unrolled across BMC depths).
/// Each abstract instantiation gets unrolled to multiple depth-indexed versions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IndexedInstantiationRecord {
    /// The label used for assert_and_track (e.g., "inst_0_1", "inst_5_depth_3")
    pub label: String,
    /// String representation of the indexed term (with frame indices like @0, @1)
    pub term: String,
    /// Canonical hash for matching to unsat core
    pub term_hash: String,
    /// BMC depth at which this indexed instantiation was added
    pub depth: u16,
    /// Index within the unroll (0 = deepest, counting back)
    pub unroll_index: u16,
    /// Stable id of the original abstract instantiation this indexed assertion came from
    pub abstract_instantiation_id: Option<String>,
    /// Whether this tracked indexed instantiation appeared in the unsat core
    pub in_unsat_core: bool,
}
