use crate::{interpolant::Interpolant, smt_problem::SMTProblem};
use serde::{Deserialize, Serialize};
use smt2parser::{get_term_from_term_string, let_extract::LetExtract};
use std::collections::BTreeMap;
use std::io::Write;
use std::{fmt::Display, fs::File, io::Error, process::Command};

use z3::Statistics;
static INTERPOLANT_FILENAME: &str = "interpolant-out.smt2";

/// Run with COMMAND_TIME_LIMIT so that we don't keep zombie ic3ia
/// runs.
pub fn run_command(cmd: &str, args: &[&str]) -> Result<String, String> {
    let output = Command::new(cmd)
        .args(args)
        .output()
        .map_err(|e| format!("Failed to execute command: {e}"))?;

    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).trim().to_string())
    }
}

pub fn run_smtinterpol(smt_problem: &SMTProblem) -> Result<Vec<Interpolant>, Error> {
    let interpolant_problem = smt_problem.to_smtinterpol();
    let mut temp_file = File::create(INTERPOLANT_FILENAME)?;
    writeln!(temp_file, "{interpolant_problem}")?;
    let interp_out = match run_command(
        "java",
        &[
            "-jar",
            "./tools/smtinterpol-2.5-1386-gcca67e02.jar",
            "-w",
            INTERPOLANT_FILENAME,
        ],
    ) {
        Ok(out) => out,
        Err(err) => panic!("{err}"),
    };

    let stdout = interp_out
        .split("\n")
        .map(|s| s.to_string())
        .collect::<Vec<_>>();

    // First element should always be 'unsat' from (check-sat) call.
    assert_eq!(stdout[0], "unsat");
    // Second element is the sequent interpolant.
    let mut interpolants = stdout[1].clone();
    // Have to add `and` to the interpolant to make it valid smt2
    interpolants.insert_str(1, "and ");
    // Format it to `assert` call so smt2parser can handle it.
    let term = get_term_from_term_string(&interpolants);
    let sequent_interpolant = LetExtract::substitute(term.clone());
    // Interpolants will now be the arguments to the `and` term created above.
    log::debug!("----------------------------------------");
    let interpolants = match sequent_interpolant {
        smt2parser::concrete::Term::Application {
            qual_identifier: _,
            arguments,
        } => arguments
            .iter()
            .enumerate()
            .map(|(interpolant_number, term)| Interpolant::from(term, interpolant_number))
            .collect(),
        _ => panic!("Sequent interpolant is not `and` application."),
    };
    Ok(interpolants)
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(untagged)]
pub enum StatisticsValue {
    UInt(u32),
    Double(f64),
}

impl Display for StatisticsValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StatisticsValue::UInt(int) => f.write_str(format!("{int}").as_str()),
            StatisticsValue::Double(float) => f.write_str(format!("{float}").as_str()),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, Default)]
pub struct SolverStatistics {
    stats: BTreeMap<String, StatisticsValue>,
}

impl SolverStatistics {
    pub fn new() -> SolverStatistics {
        SolverStatistics {
            stats: BTreeMap::new(),
        }
    }

    pub fn join_from_z3_statistics(&mut self, z3_stats: Statistics) {
        for entry in z3_stats.entries() {
            let key = entry.key;
            let value = match entry.value {
                z3::StatisticsValue::UInt(int_num) => StatisticsValue::UInt(int_num),
                z3::StatisticsValue::Double(float_num) => StatisticsValue::Double(float_num),
            };
            self.stats.insert(key, value);
        }
    }

    /// Add or accumulate a custom timing measurement (in seconds)
    pub fn add_time(&mut self, key: &str, duration_secs: f64) {
        if let Some(StatisticsValue::Double(prev_value)) = self.stats.get(key) {
            self.stats.insert(
                key.to_string(),
                StatisticsValue::Double(prev_value + duration_secs),
            );
        } else {
            self.stats
                .insert(key.to_string(), StatisticsValue::Double(duration_secs));
        }
    }
}
