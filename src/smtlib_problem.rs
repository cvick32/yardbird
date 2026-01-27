use smt2parser::concrete::{Command, SyntaxBuilder, Term};
use smt2parser::let_extract::LetExtract;
use smt2parser::vmt::array_abstractor::ArrayAbstractor;
use smt2parser::CommandStream;
use std::path::Path;

use crate::problem::Problem;
use crate::smtlib_smt_problem::SMTLIBSMTProblem;
use crate::strategies::{ProofAction, ProofStrategy};
use crate::utils::SolverStatistics;
use crate::z3_var_context::Z3VarContext;
use crate::ProofLoopResult;

/// Represents an SMTLIB problem (non-transition system)
/// Supports both incremental (multiple check-sat with push/pop) and
/// non-incremental (single check-sat) solving
#[derive(Clone, Debug)]
pub struct SMTLIBProblem {
    /// All commands from the .smt2 file in order
    commands: Vec<Command>,

    /// Logic string (from set-logic command)
    logic: Option<String>,

    /// Sort declarations
    sorts: Vec<Command>,

    /// Function and constant declarations
    function_definitions: Vec<Command>,

    /// Assertion commands
    assertions: Vec<Command>,

    /// Locations where check-sat appears (indices in the command stream)
    check_sat_positions: Vec<usize>,

    /// Whether this problem uses incremental solving (has push/pop)
    is_incremental: bool,
}

#[derive(Debug)]
pub enum SMTLIBError {
    FileError,
    ParseError,
}

impl From<std::io::Error> for SMTLIBError {
    fn from(_value: std::io::Error) -> Self {
        SMTLIBError::FileError
    }
}

impl From<smt2parser::concrete::Error> for SMTLIBError {
    fn from(_value: smt2parser::concrete::Error) -> Self {
        SMTLIBError::ParseError
    }
}

impl SMTLIBProblem {
    pub fn as_smt2_string(&self) -> String {
        use itertools::Itertools;
        self.commands
            .iter()
            .map(|command| format!("{}", command.clone().accept(&mut SyntaxBuilder).unwrap()))
            .join("\n")
    }

    fn preprocess_commands(commands: Vec<Command>) -> Vec<Command> {
        commands
            .into_iter()
            .map(|cmd| match cmd {
                Command::Assert { term } => Command::Assert {
                    term: LetExtract::substitute(term),
                },
                Command::DefineFun { sig, term } => Command::DefineFun {
                    sig,
                    term: LetExtract::substitute(term),
                },
                other => other,
            })
            .collect()
    }

    /// Parse an SMTLIB file from a path
    pub fn from_path(path: impl AsRef<Path>) -> Result<Self, SMTLIBError> {
        let file = std::fs::File::open(path.as_ref())?;
        let reader = std::io::BufReader::new(file);
        let command_stream = CommandStream::new(
            reader,
            SyntaxBuilder,
            Some(path.as_ref().to_string_lossy().to_string()),
        );

        let commands: Vec<Command> = command_stream.into_iter().collect::<Result<Vec<_>, _>>()?;

        Self::from_commands(commands)
    }

    /// Create an SMTLIBProblem from a list of commands
    pub fn from_commands(commands: Vec<Command>) -> Result<Self, SMTLIBError> {
        let commands = Self::preprocess_commands(commands);
        let mut logic = None;
        let mut sorts = Vec::new();
        let mut function_definitions = Vec::new();
        let mut assertions = Vec::new();
        let mut check_sat_positions = Vec::new();
        let mut is_incremental = false;

        for (idx, command) in commands.iter().enumerate() {
            match command {
                Command::SetLogic { symbol } => {
                    logic = Some(symbol.0.clone());
                }
                Command::DeclareSort { .. } => {
                    sorts.push(command.clone());
                }
                Command::DeclareFun { .. } | Command::DeclareConst { .. } => {
                    function_definitions.push(command.clone());
                }
                Command::DefineFun { .. } => {
                    function_definitions.push(command.clone());
                }
                Command::Assert { .. } => {
                    assertions.push(command.clone());
                }
                Command::CheckSat | Command::CheckSatAssuming { .. } => {
                    check_sat_positions.push(idx);
                }
                Command::Push { .. } | Command::Pop { .. } => {
                    is_incremental = true;
                }
                _ => {
                    // Ignore other commands (get-model, set-option, etc.)
                }
            }
        }

        Ok(SMTLIBProblem {
            commands,
            logic,
            sorts,
            function_definitions,
            assertions,
            check_sat_positions,
            is_incremental,
        })
    }

    /// Returns true if this problem uses incremental solving (has push/pop)
    pub fn is_incremental(&self) -> bool {
        self.is_incremental
    }

    pub fn num_check_sats(&self) -> usize {
        self.check_sat_positions.len()
    }

    pub fn get_commands(&self) -> &[Command] {
        &self.commands
    }

    pub fn get_assertions(&self) -> &[Command] {
        &self.assertions
    }

    /// Abstract array theory (select/store operations) into uninterpreted functions (Read/Write).
    /// Returns (abstracted_problem, discovered_array_types) where discovered_array_types is a vector
    /// of (index_sort, value_sort) pairs for all array types found in the problem.
    pub fn abstract_array_theory(&self) -> (SMTLIBProblem, Vec<(String, String)>) {
        let mut abstractor = ArrayAbstractor::default();
        let mut abstracted_commands = vec![];

        for command in &self.commands {
            abstracted_commands.push(command.clone().accept(&mut abstractor).unwrap());
        }

        // Add array type definitions at the beginning
        let mut array_definitions = abstractor.get_array_type_definitions();
        array_definitions.extend(abstracted_commands);

        // Extract discovered types from the abstractor
        let discovered_types: Vec<(String, String)> = abstractor.array_types.into_iter().collect();

        (
            SMTLIBProblem::from_commands(array_definitions).unwrap(),
            discovered_types,
        )
    }

    /// Get assertion terms for subterm extraction
    pub fn get_assertion_terms(&self) -> Vec<Term> {
        self.assertions
            .iter()
            .filter_map(|cmd| match cmd {
                Command::Assert { term } => Some(term.clone()),
                _ => None,
            })
            .collect()
    }
}

impl Problem for SMTLIBProblem {
    fn get_sorts(&self) -> Vec<Command> {
        self.sorts.clone()
    }

    fn get_function_definitions(&self) -> Vec<Command> {
        self.function_definitions.clone()
    }

    fn get_logic(&self) -> Option<String> {
        self.logic.clone()
    }

    fn requires_unrolling(&self) -> bool {
        false
    }

    fn as_commands(&self) -> Vec<Command> {
        self.commands.clone()
    }

    fn check(&mut self) -> z3::SatResult {
        todo!()
    }

    fn unroll(&mut self, _depth: u16) {
        // SMTLIB problems don't require unrolling
    }

    fn add_instantiation(&self, _term: &Term) {
        todo!()
    }
}

/// Result of a single check-sat command
#[derive(Debug, Clone)]
pub struct CheckSatResult {
    /// The satisfiability result
    pub result: z3::SatResult,
    /// The index of the check-sat command in the original command stream
    pub command_index: usize,
    /// Model if sat (only stored if explicitly requested)
    pub model: Option<String>,
}

/// Solver for executing SMTLIB problems
/// Handles incremental solving with push/pop and multiple check-sat commands
pub struct SMTLIBSolver {
    z3_var_context: Z3VarContext,
    solver: z3::Solver,
    solver_statistics: SolverStatistics,
    check_sat_results: Vec<CheckSatResult>,
}

impl SMTLIBSolver {
    /// Create a new SMTLIB solver with the given logic
    pub fn new(logic: Option<String>) -> Self {
        let solver = if let Some(logic_str) = logic {
            z3::Solver::new_for_logic(logic_str.as_str()).unwrap()
        } else {
            // Default to QF_UFLIA if no logic specified
            z3::Solver::new_for_logic("QF_UFLIA").unwrap()
        };

        SMTLIBSolver {
            z3_var_context: Z3VarContext::new(),
            solver,
            solver_statistics: SolverStatistics::new(),
            check_sat_results: Vec::new(),
        }
    }

    /// Execute all commands from an SMTLIB problem
    pub fn execute(&mut self, problem: &SMTLIBProblem) {
        for (idx, command) in problem.get_commands().iter().enumerate() {
            self.execute_command(command, idx);
        }
    }

    /// Execute a single command
    fn execute_command(&mut self, command: &Command, command_index: usize) {
        match command {
            Command::Assert { term } => {
                self.handle_assert(term);
            }
            Command::CheckSat => {
                let result = self.handle_check_sat(command_index);
                self.check_sat_results.push(result);
            }
            Command::CheckSatAssuming { literals } => {
                let result = self.handle_check_sat_assuming(command_index, literals);
                self.check_sat_results.push(result);
            }
            Command::Push { level } => {
                let num_levels: u32 = level.try_into().unwrap_or(1);
                for _ in 0..num_levels {
                    self.solver.push();
                }
            }
            Command::Pop { level } => {
                let num_levels: u32 = level.try_into().unwrap_or(1);
                self.solver.pop(num_levels);
            }
            Command::DeclareFun { .. }
            | Command::DeclareConst { .. }
            | Command::DefineFun { .. }
            | Command::DeclareSort { .. } => {
                // Handle declarations through Z3VarContext
                let _ = command.clone().accept(&mut self.z3_var_context);
            }
            Command::SetLogic { .. } | Command::SetOption { .. } | Command::SetInfo { .. } => {
                // Ignore these - already handled during problem construction
            }
            _ => {
                // Ignore other commands (get-model, exit, etc.)
            }
        }
    }

    /// Handle an assert command
    fn handle_assert(&mut self, term: &Term) {
        let z3_term = self.z3_var_context.rewrite_term(term);
        self.solver.assert(z3_term.as_bool().unwrap());
    }

    /// Handle a check-sat command
    fn handle_check_sat(&mut self, command_index: usize) -> CheckSatResult {
        let start_time = std::time::Instant::now();
        let result = self.solver.check();

        // Update statistics
        self.solver_statistics
            .join_from_z3_statistics(self.solver.get_statistics());
        let check_duration = start_time.elapsed();
        self.solver_statistics
            .add_time("solver_time", check_duration.as_secs_f64());

        CheckSatResult {
            result,
            command_index,
            model: None, // Can extend later to capture models
        }
    }

    /// Handle a check-sat-assuming command
    fn handle_check_sat_assuming(
        &mut self,
        command_index: usize,
        literals: &[(smt2parser::concrete::Symbol, bool)],
    ) -> CheckSatResult {
        use smt2parser::concrete::{Identifier, QualIdentifier};

        // Convert assumptions to terms and assert them temporarily
        self.solver.push();

        for (symbol, polarity) in literals {
            let qual_id = QualIdentifier::Simple {
                identifier: Identifier::Simple {
                    symbol: symbol.clone(),
                },
            };
            let term = Term::QualIdentifier(qual_id);
            let z3_var = self.z3_var_context.rewrite_term(&term);

            if *polarity {
                self.solver.assert(z3_var.as_bool().unwrap());
            } else {
                self.solver
                    .assert(z3::ast::Bool::not(&z3_var.as_bool().unwrap()));
            }
        }

        let result = self.handle_check_sat(command_index);
        self.solver.pop(1);
        result
    }

    /// Get all check-sat results
    pub fn get_results(&self) -> &[CheckSatResult] {
        &self.check_sat_results
    }

    /// Get solver statistics
    pub fn get_statistics(&self) -> &SolverStatistics {
        &self.solver_statistics
    }

    /// Execute with abstract/concrete strategy (refinement loop)
    /// This is the strategy-based solving mode with refinement
    #[allow(clippy::borrowed_box)]
    pub fn execute_with_strategy<S>(
        problem: &SMTLIBProblem,
        mut strategy: Box<dyn ProofStrategy<'_, S>>,
        max_refinements: u32,
        //  instantiation_strategy: Box<dyn InstantiationStrategy>,
    ) -> anyhow::Result<(ProofLoopResult, Option<SMTLIBProblem>)> {
        use log::info;

        // 1. Abstract if needed
        let (working_problem, array_types) = if strategy.get_theory_support().requires_abstraction()
        {
            info!("Abstracting array theory");
            let (abs_problem, types) = problem.abstract_array_theory();
            info!("Discovered array types: {:?}", types);
            (abs_problem, types)
        } else {
            (problem.clone(), vec![])
        };

        // Store the abstracted problem for potential output
        let abstracted_problem = if strategy.get_theory_support().requires_abstraction() {
            Some(working_problem.clone())
        } else {
            None
        };

        info!(
            "Starting refinement loop with max {} iterations",
            max_refinements
        );

        // 2. Create wrapper with array types for correct logic string
        let mut smt_problem = SMTLIBSMTProblem::new_with_array_types(
            &working_problem,
            &strategy,
            false, // track_instantiations - TODO: make this configurable
            //instantiation_strategy,
            array_types,
        );

        // 3. Refinement loop (similar to Driver::check_strategy but no depths)
        let mut found_proof = false;
        let mut counterexample = false;

        for refinement_step in 0..max_refinements {
            info!("Refinement iteration {}", refinement_step + 1);

            let mut state = strategy.setup(&smt_problem, 0)?;

            let action = match smt_problem.check() {
                z3::SatResult::Unsat => {
                    info!("  Result: UNSAT");
                    strategy.unsat(&mut state, &smt_problem)?
                }
                z3::SatResult::Sat => {
                    info!("  Result: SAT");
                    strategy.sat(&mut state, &smt_problem, refinement_step)?
                }
                z3::SatResult::Unknown => {
                    info!(
                        "  Result: UNKNOWN - {}",
                        smt_problem
                            .get_reason_unknown()
                            .unwrap_or_else(|| "no reason given".to_string())
                    );
                    strategy.unknown(&mut state, &smt_problem)?
                }
            };

            match action {
                ProofAction::Continue => {
                    info!("  Action: Continue refinement");
                    strategy.finish(state, &mut smt_problem)?;
                }
                ProofAction::FoundProof => {
                    info!("  Action: Found proof!");
                    found_proof = true;
                    strategy.finish(state, &mut smt_problem)?;
                    break;
                }
                ProofAction::NextDepth => {
                    // For SMTLIB (no depths), treat this as completion
                    info!("  Action: Refinement complete");
                    strategy.finish(state, &mut smt_problem)?;
                    break;
                }
                ProofAction::FoundCounterexample => {
                    info!("  Action: Found counterexample");
                    counterexample = true;
                    strategy.finish(state, &mut smt_problem)?;
                    break;
                }
            }
        }

        // 4. Build result
        info!(
            "Refinement complete. Total instantiations: {}",
            smt_problem.get_number_instantiations_added()
        );

        Ok((
            ProofLoopResult {
                model: None, // No VMT model in SMTLIB mode
                used_instances: smt_problem.get_instantiations(),
                const_instances: vec![], // TODO: track const instances separately if needed
                total_instantiations_added: smt_problem.get_number_instantiations_added(),
                solver_statistics: smt_problem.get_solver_statistics(),
                counterexample,
                found_proof,
            },
            abstracted_problem,
        ))
    }
}
