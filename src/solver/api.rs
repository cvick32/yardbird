#[derive(Copy, Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum SolverCheckResult {
    Sat,
    Unsat,
    Unknown,
}
