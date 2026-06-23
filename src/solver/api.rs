#[derive(Copy, Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum SolverCheckResult {
    Sat,
    Unsat,
    Unknown,
}

impl From<z3::SatResult> for SolverCheckResult {
    fn from(result: z3::SatResult) -> Self {
        match result {
            z3::SatResult::Sat => SolverCheckResult::Sat,
            z3::SatResult::Unsat => SolverCheckResult::Unsat,
            z3::SatResult::Unknown => SolverCheckResult::Unknown,
        }
    }
}
