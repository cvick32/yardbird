use smt2parser::concrete::{Command, SyntaxBuilder, Term};
use smt2parser::CommandStream;
use std::path::Path;

use crate::problem::Problem;
use crate::utils::SolverStatistics;
use crate::z3_var_context::Z3VarContext;

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
}
