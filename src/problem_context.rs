use smt2parser::concrete::Term;
use smt2parser::vmt::{
    quantified_instantiator::{Instance, UnquantifiedInstantiator},
    variable::Variable,
    ReadsAndWrites,
};
use std::any::Any;

use crate::{
    auxiliary_synthesis::{AuxiliaryRecord, AuxiliarySpec},
    instantiation_provenance::{
        InstantiationInstallResult, InstantiationProvenance, InstantiationRequest,
    },
    utils::SolverStatistics,
};

/// Candidate terms and array-operation sites with the same provenance.
#[derive(Clone, Default)]
pub struct ArrayCandidatePool {
    pub terms: Vec<String>,
    pub reads_and_writes: ReadsAndWrites,
}

/// Keeps problem-authored candidates separate from terms introduced by refinement.
///
/// Derived terms remain available to full refinement, but they must not silently
/// become source sites merely because an earlier instantiation was asserted.
#[derive(Clone, Default)]
pub struct ArrayCandidateCatalog {
    pub source_grounded: ArrayCandidatePool,
    pub derived: ArrayCandidatePool,
}

/// Common refinement context that proof strategies can work with.
///
/// This sits above the solver backend and exposes problem-specific data such as
/// subterms, VMT variables, instantiation bookkeeping, and discovered array types.
/// Implemented by both VmtBmcSession and SmtlibRefinementSession.
pub trait ProblemContext {
    /// Enable downcasting to concrete types
    fn as_any(&self) -> &dyn Any;
    fn has_model(&self) -> bool;
    fn eval_to_string(&self, term: &Term) -> anyhow::Result<String>;
    fn model_to_string(&self) -> anyhow::Result<String>;
    fn get_all_subterms(&self) -> Vec<&Term>;
    /// Get only problem-authored subterms, excluding formulas introduced by
    /// refinement. Backends without separate provenance use all subterms.
    fn get_source_subterms(&self) -> Vec<&Term> {
        self.get_all_subterms()
    }
    /// Whether source and refinement-authored subterms have distinct provenance.
    fn separates_source_subterms(&self) -> bool {
        false
    }
    fn get_solver_statistics(&self) -> SolverStatistics;
    fn get_reason_unknown(&self) -> Option<String>;

    // Methods for instantiation management
    fn add_instantiation(&mut self, request: InstantiationRequest) -> InstantiationInstallResult;
    fn get_instantiations(&self) -> Vec<Term>;
    fn get_variables(&self) -> &[Variable];
    fn get_number_instantiations_added(&self) -> u64;

    fn make_unquantified_instance(&self, term: Term) -> Option<Instance> {
        UnquantifiedInstantiator::rewrite_unquantified(term, self.get_variables().to_vec())
    }

    fn make_provenanced_unquantified_instance(
        &self,
        term: Term,
        provenance: InstantiationProvenance,
    ) -> Option<InstantiationRequest> {
        let (abstract_instantiation_id, substitution) = provenance.into_parts();
        let (inst, relative_substitution) =
            UnquantifiedInstantiator::rewrite_unquantified_with_substitution(
                term,
                self.get_variables().to_vec(),
                substitution,
            )?;
        Some(InstantiationRequest::provenanced(
            inst,
            InstantiationProvenance::new(abstract_instantiation_id, relative_substitution),
        ))
    }

    /// Number of post-materialization assertions actually sent to the solver.
    fn get_number_instantiation_assertions_added(&self) -> u64;

    // Methods for cost functions
    /// Get subterms from initial state and transition relation (VMT-specific, empty for SMTLIB)
    fn get_init_and_transition_subterms(&self) -> Vec<String>;
    /// Get only problem-authored initial/transition subterms.
    fn get_source_init_and_transition_subterms(&self) -> Vec<String> {
        self.get_init_and_transition_subterms()
    }
    /// Get subterms from property (for SMTLIB, this is all assertion subterms)
    fn get_property_subterms(&self) -> Vec<String>;
    /// Get reads and writes from the problem
    fn get_reads_and_writes(&self) -> ReadsAndWrites;

    /// Return array-refinement candidates grouped by provenance.
    ///
    /// Backends without separate refinement bookkeeping can treat all of their
    /// terms as source-grounded.
    fn get_array_candidate_catalog(&self) -> ArrayCandidateCatalog {
        let mut source_terms = self.get_init_and_transition_subterms();
        source_terms.extend(self.get_property_subterms());
        ArrayCandidateCatalog {
            source_grounded: ArrayCandidatePool {
                terms: source_terms,
                reads_and_writes: self.get_reads_and_writes(),
            },
            derived: ArrayCandidatePool::default(),
        }
    }

    /// Get discovered array types (index_sort, value_sort) pairs
    fn get_array_types(&self) -> Vec<(String, String)>;

    /// Materialize a source-level transition formula at one concrete BMC
    /// frame. Stateless SMT-LIB problems have no transition frames.
    fn frame_transition_formula(&self, _term: Term, _frame: u16) -> Option<Term> {
        None
    }

    fn install_auxiliary_specs(&mut self, _specs: Vec<AuxiliarySpec>) -> anyhow::Result<()> {
        Ok(())
    }

    fn get_auxiliary_records(&self) -> Vec<AuxiliaryRecord> {
        vec![]
    }

    fn get_auxiliary_specs(&self) -> Vec<AuxiliarySpec> {
        vec![]
    }
}
