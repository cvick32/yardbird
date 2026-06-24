use log::debug;
use smt2parser::{
    concrete::{Command, Identifier, QualIdentifier, Symbol, Term},
    vmt::{quantified_instantiator::Instance, ReadsAndWrites},
};

use crate::{
    instantiation_strategy::StoredInstantiation,
    problem::Problem,
    smtlib_problem::SMTLIBProblem,
    solver::{new_solver_backend, SolverCheckResult, YardbirdSolver},
    solver_interface::SolverInterface,
    strategies::ProofStrategy,
    subterm_handler::SubtermHandler,
    training::IndexedInstantiationRecord,
    utils::SolverStatistics,
    SolverBackend,
};

/// Helper to create a "true" boolean term
fn make_true_term() -> Term {
    Term::QualIdentifier(QualIdentifier::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol("true".to_string()),
        },
    })
}

/// Wrapper around SMTLIBProblem that provides the interface strategies expect
/// Similar to SMTProblem but for stateless SMTLIB problems (no temporal reasoning)
pub struct SMTLIBSMTProblem {
    solver: Box<dyn YardbirdSolver>,
    original_problem: SMTLIBProblem,
    assertions: Vec<Term>,
    depth: u16, // Always 0 (no temporal unrolling)
    instantiations: Vec<StoredInstantiation>,
    subterm_handler: SubtermHandler,
    num_quantifiers_instantiated: u64,
    track_instantiations: bool,
    tracked_labels: Vec<IndexedInstantiationRecord>,
    //instantiation_strategy: Box<dyn InstantiationStrategy>,
    /// Discovered array types (index_sort, value_sort) pairs
    array_types: Vec<(String, String)>,
}

impl std::fmt::Debug for SMTLIBSMTProblem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SMTLIBSMTProblem")
            .field("depth", &self.depth)
            .field(
                "num_quantifiers_instantiated",
                &self.num_quantifiers_instantiated,
            )
            .field("track_instantiations", &self.track_instantiations)
            .field("num_assertions", &self.assertions.len())
            .finish_non_exhaustive()
    }
}

impl Clone for SMTLIBSMTProblem {
    fn clone(&self) -> Self {
        // SMTLIBSMTProblem contains non-cloneable solver objects and models.
        unimplemented!(
            "SMTLIBSMTProblem::clone() is not implemented due to non-cloneable solver objects"
        )
    }
}

/// Helper to extract assertions from a problem
fn extract_assertions(problem: &SMTLIBProblem) -> Vec<Term> {
    problem
        .get_assertions()
        .iter()
        .filter_map(|cmd| match cmd {
            Command::Assert { term } => Some(term.clone()),
            _ => None,
        })
        .collect()
}

/// Helper to combine assertions into a single term
fn combine_assertions(assertions: &[Term]) -> Term {
    if assertions.is_empty() {
        make_true_term()
    } else if assertions.len() == 1 {
        assertions[0].clone()
    } else {
        Term::Application {
            qual_identifier: QualIdentifier::Simple {
                identifier: Identifier::Simple {
                    symbol: Symbol("and".to_string()),
                },
            },
            arguments: assertions.to_vec(),
        }
    }
}

#[allow(clippy::borrowed_box)]
impl SMTLIBSMTProblem {
    /// Common initialization logic for constructors
    fn init_common(
        problem: &SMTLIBProblem,
        theory: &dyn crate::theory_support::TheorySupport,
        solver: Box<dyn YardbirdSolver>,
        track_instantiations: bool,
        array_types: Vec<(String, String)>,
    ) -> Self {
        let assertions = extract_assertions(problem);
        let combined_assertion = combine_assertions(&assertions);

        let mut smt = SMTLIBSMTProblem {
            subterm_handler: SubtermHandler::new(
                make_true_term(),
                make_true_term(),
                combined_assertion,
            ),
            assertions,
            instantiations: vec![],
            depth: 0,
            solver,
            num_quantifiers_instantiated: 0,
            track_instantiations,
            tracked_labels: vec![],
            original_problem: problem.clone(),
            array_types,
        };

        // Handle theory-specific function declarations
        if theory.requires_abstraction() {
            for function_def in problem.get_function_definitions() {
                smt.solver
                    .accept_command(&function_def)
                    .expect("solver should accept SMT-LIB function declarations");
            }
        }

        // Add sort declarations
        for sort_decl in problem.get_sorts() {
            smt.solver
                .accept_command(&sort_decl)
                .expect("solver should accept SMT-LIB sort declarations");
        }

        // Add uninterpreted functions declared by the theory
        for func_decl in theory.get_uninterpreted_functions() {
            let command = func_decl.to_command();
            smt.solver
                .accept_command(&command)
                .expect("solver should accept theory function declarations");
        }

        // Add axioms declared by the theory
        let axiom_formulas = theory.get_axiom_formulas();
        if !axiom_formulas.is_empty() {
            debug!("Adding {} axioms to solver", axiom_formulas.len());
        }
        for axiom_command in axiom_formulas {
            if let Command::Assert { term } = axiom_command {
                if let Term::Forall { vars, term: _ } = &term {
                    for (symbol, sort) in vars {
                        smt.solver
                            .create_variable(symbol, sort)
                            .expect("solver should create quantified axiom variables");
                    }
                }
                smt.solver
                    .assert_term(&term)
                    .expect("solver should assert theory axioms");
            }
        }

        debug!("{:#?}", smt);

        // Add assertions to solver
        smt.add_assertions();

        smt
    }

    /// Create a new SMTLIBSMTProblem from an SMTLIB problem and strategy
    pub fn new<S>(
        problem: &SMTLIBProblem,
        strategy: &Box<dyn ProofStrategy<'_, S>>,
        solver_backend: SolverBackend,
        track_instantiations: bool,
    ) -> Self {
        let theory = strategy.get_theory_support();
        let solver = new_solver_backend(solver_backend, &theory.get_logic_string());
        Self::init_common(
            problem,
            theory.as_ref(),
            solver,
            track_instantiations,
            vec![],
        )
    }

    /// Create a new SMTLIBSMTProblem with explicit array types for correct logic detection.
    /// This is used when the array types are discovered during abstraction.
    pub fn new_with_array_types<S>(
        problem: &SMTLIBProblem,
        strategy: &Box<dyn ProofStrategy<'_, S>>,
        solver_backend: SolverBackend,
        track_instantiations: bool,
        array_types: Vec<(String, String)>,
    ) -> Self {
        use crate::theory_support::{ArrayTheorySupport, ArrayWithQuantifiersTheorySupport};

        let stored_array_types = array_types.clone();
        let original_theory = strategy.get_theory_support();

        // Create theory support with discovered array types for correct logic string
        let theory: Box<dyn crate::theory_support::TheorySupport> = if array_types.is_empty() {
            original_theory
        } else if original_theory.uses_quantified_axioms() {
            debug!("Using ArrayWithQuantifiersTheorySupport for axiom generation");
            Box::new(ArrayWithQuantifiersTheorySupport::new(array_types))
        } else {
            debug!("Using ArrayTheorySupport (no axioms)");
            Box::new(ArrayTheorySupport::new(array_types))
        };

        let logic_string = theory.get_logic_string();
        debug!("Using logic: {}", logic_string);
        let solver = new_solver_backend(solver_backend, logic_string.as_str());

        Self::init_common(
            problem,
            theory.as_ref(),
            solver,
            track_instantiations,
            stored_array_types,
        )
    }

    /// Add all assertions to the solver
    fn add_assertions(&mut self) {
        for term in &self.assertions {
            self.solver
                .assert_term(term)
                .expect("solver should assert SMT-LIB assertions");
        }
    }

    pub fn add_instantiation(
        &mut self,
        inst: Instance,
        abstract_instantiation_id: Option<String>,
    ) -> bool {
        let initial_count = self.instantiations.len();

        // For SMTLIB, we don't have a BMCBuilder, so we pass dummy values
        // The instantiation strategy might need to be adapted for SMTLIB
        let term = inst.get_term();

        // Add the instantiation directly to the solver
        if self.track_instantiations {
            // Generate a unique label for tracking
            let label_name = format!("inst_{}", self.num_quantifiers_instantiated);

            // Use assert_and_track so the label appears in unsat core
            self.solver
                .assert_tracked_term(term, label_name.as_str())
                .expect("solver should assert tracked SMT-LIB instantiations");
            let term_string = term.to_string();
            self.tracked_labels.push(IndexedInstantiationRecord {
                label: label_name,
                term: term_string.clone(),
                term_hash: crate::training::canonical_term_hash_from_string(&term_string),
                depth: 0,
                unroll_index: 0,
                abstract_instantiation_id: abstract_instantiation_id.clone(),
                in_unsat_core: false,
            });
        } else {
            self.solver
                .assert_term(term)
                .expect("solver should assert SMT-LIB instantiations");
        }

        self.instantiations.push(StoredInstantiation {
            inst,
            abstract_instantiation_id,
        });
        self.num_quantifiers_instantiated += 1;

        // Return true if a new instantiation was added
        self.instantiations.len() > initial_count
    }

    pub fn get_solver_statistics(&self) -> SolverStatistics {
        self.solver.get_solver_statistics()
    }

    pub fn get_reason_unknown(&self) -> Option<String> {
        self.solver.get_reason_unknown()
    }

    pub fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
        self.solver.eval_to_string(term)
    }

    pub fn get_all_subterms(&self) -> Vec<&Term> {
        // For SMTLIB, we return references to all assertion terms
        self.assertions.iter().collect()
    }

    pub fn get_instantiations(&self) -> Vec<Term> {
        self.instantiations
            .iter()
            .map(|stored| stored.inst.get_term().clone())
            .collect()
    }

    pub fn get_number_instantiations_added(&self) -> u64 {
        self.num_quantifiers_instantiated
    }

    /// Check satisfiability of the current problem
    /// Unlike SMTProblem, we don't push/pop property since all assertions are already in the solver
    pub fn check(&mut self) -> SolverCheckResult {
        self.solver.check_and_record_statistics()
    }

    /// Dump the solver state to an SMT2 file
    pub fn dump_solver_to_file(&self, path: &str) -> anyhow::Result<()> {
        use std::fs::File;
        use std::io::Write;

        let smt2_string = self.solver.to_smt2_string()?;
        let mut file = File::create(path)?;
        file.write_all(smt2_string.as_bytes())?;
        Ok(())
    }

    /// Get the unsat core when tracking is enabled
    pub fn get_unsat_core(&self) -> Option<Vec<String>> {
        if !self.track_instantiations {
            return None;
        }

        self.solver.get_unsat_core().ok()
    }

    /// Get the tracked labels for unsat core analysis
    pub fn get_tracked_labels(&self) -> &[IndexedInstantiationRecord] {
        &self.tracked_labels
    }

    /// Generate SMT2 string with abstracted functions and added instantiations
    pub fn as_smt2_string_with_instantiations(&self) -> String {
        use itertools::Itertools;
        use smt2parser::concrete::SyntaxBuilder;

        let mut commands = vec![];

        // Add logic if present
        if let Some(logic) = self.original_problem.get_logic() {
            commands.push(Command::SetLogic {
                symbol: smt2parser::concrete::Symbol(logic),
            });
        }

        // Add sorts
        commands.extend(self.original_problem.get_sorts());

        // Add function definitions
        commands.extend(self.original_problem.get_function_definitions());

        // Add original assertions
        commands.extend(self.original_problem.get_assertions().to_vec());

        // Add instantiations as asserts
        for inst in &self.instantiations {
            commands.push(Command::Assert {
                term: inst.inst.get_term().clone(),
            });
        }

        // Add check-sat
        commands.push(Command::CheckSat);

        // Convert to SMT2 string
        commands
            .iter()
            .map(|cmd| format!("{}", cmd.clone().accept(&mut SyntaxBuilder).unwrap()))
            .join("\n")
    }
}

impl SolverInterface for SMTLIBSMTProblem {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn has_model(&self) -> bool {
        self.solver.has_model()
    }

    fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
        self.solver.eval_to_string(term)
    }

    fn model_to_string(&self) -> anyhow::Result<String> {
        self.solver.model_to_string()
    }

    fn get_all_subterms(&self) -> Vec<&Term> {
        self.assertions.iter().collect()
    }

    fn get_solver_statistics(&self) -> SolverStatistics {
        self.solver.get_solver_statistics()
    }

    fn get_reason_unknown(&self) -> Option<String> {
        self.solver.get_reason_unknown()
    }

    fn add_instantiation(
        &mut self,
        inst: Instance,
        abstract_instantiation_id: Option<String>,
    ) -> bool {
        self.add_instantiation(inst, abstract_instantiation_id)
    }

    fn get_instantiations(&self) -> Vec<Term> {
        self.get_instantiations()
    }

    fn get_variables(&self) -> &[smt2parser::vmt::variable::Variable] {
        // SMTLIB problems don't have VMT-style state variables
        &[]
    }

    fn get_number_instantiations_added(&self) -> u64 {
        self.num_quantifiers_instantiated
    }

    fn get_init_and_transition_subterms(&self) -> Vec<String> {
        // SMTLIB problems don't have init/transition (no temporal reasoning)
        vec![]
    }

    fn get_property_subterms(&self) -> Vec<String> {
        // For SMTLIB, treat all assertion subterms as "property" subterms
        self.subterm_handler.get_property_subterms()
    }

    fn get_reads_and_writes(&self) -> ReadsAndWrites {
        // Extract reads and writes from all assertions
        let mut reads_and_writes = ReadsAndWrites::default();
        for term in &self.assertions {
            let _ = term.clone().accept_term_visitor(&mut reads_and_writes);
        }
        reads_and_writes
    }

    fn get_array_types(&self) -> Vec<(String, String)> {
        self.array_types.clone()
    }
}
