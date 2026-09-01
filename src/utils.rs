use crate::{
    interpolant::{
        Interpolant, SequenceInterpolantPartition, SequenceInterpolants, SequenceInterpolationQuery,
    },
    vmt_bmc_session::VmtBmcSession,
};
use serde::{Deserialize, Serialize};
use serde_json::{Map as JsonMap, Number as JsonNumber, Value as JsonValue};
use smt2parser::get_term_from_term_string;
use std::collections::BTreeMap;
use std::io::{Error, ErrorKind, Write};
use std::{fmt::Display, process::Command};

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

pub fn run_smtinterpol(smt_problem: &VmtBmcSession) -> Result<Vec<Interpolant>, Error> {
    Ok(run_sequence_smtinterpol(smt_problem)?
        .partitions
        .into_iter()
        .map(|partition| partition.interpolant)
        .collect())
}

pub fn run_sequence_smtinterpol(
    smt_problem: &VmtBmcSession,
) -> Result<SequenceInterpolants, Error> {
    let query = smt_problem.to_sequence_smtinterpol();
    validate_smtinterpol_logic(&query.logic)?;
    let interp_out = run_smtinterpol_query(&query)?;
    parse_sequence_smtinterpol_output(query, &interp_out)
}

fn parse_sequence_smtinterpol_output(
    query: SequenceInterpolationQuery,
    interp_out: &str,
) -> Result<SequenceInterpolants, Error> {
    let interpolants = parse_smtinterpol_output(interp_out)?;
    if interpolants.len() != query.interpolant_frames.len() {
        return Err(Error::new(
            ErrorKind::InvalidData,
            format!(
                "SMTInterpol returned {} interpolants for {} frame boundaries",
                interpolants.len(),
                query.interpolant_frames.len()
            ),
        ));
    }
    let partitions = query
        .interpolant_frames
        .into_iter()
        .zip(interpolants)
        .map(|(frame, interpolant)| SequenceInterpolantPartition { frame, interpolant })
        .collect();
    Ok(SequenceInterpolants::new(
        query.depth,
        query.logic,
        partitions,
    ))
}

fn validate_smtinterpol_logic(logic: &str) -> Result<(), Error> {
    if logic == "ALL" || logic.contains("BV") {
        return Err(Error::new(
            ErrorKind::Unsupported,
            format!("SMTInterpol does not support Yardbird interpolation logic {logic}"),
        ));
    }
    Ok(())
}

fn run_smtinterpol_query(query: &SequenceInterpolationQuery) -> Result<String, Error> {
    let mut temp_file = tempfile::NamedTempFile::new()?;
    writeln!(temp_file, "{}", query.smt2)?;
    let temp_path = temp_file
        .path()
        .to_str()
        .ok_or_else(|| Error::new(ErrorKind::InvalidInput, "non-UTF8 SMTInterpol temp path"))?;
    match run_command(
        "java",
        &[
            "-jar",
            "./tools/smtinterpol-2.5-1386-gcca67e02.jar",
            "-w",
            temp_path,
        ],
    ) {
        Ok(out) => Ok(out),
        Err(err) => Err(Error::other(err)),
    }
}

fn parse_smtinterpol_output(interp_out: &str) -> Result<Vec<Interpolant>, Error> {
    let stdout = interp_out
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>();
    // First element should always be 'unsat' from (check-sat) call.
    let Some(status) = stdout.first() else {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "SMTInterpol produced no output",
        ));
    };
    if *status != "unsat" {
        return Err(Error::new(
            ErrorKind::InvalidData,
            format!("SMTInterpol did not return unsat: {status}"),
        ));
    }
    // The sequent interpolant may span multiple lines.
    let mut interpolants = stdout[1..].join(" ");
    if !interpolants.starts_with('(') {
        return Err(Error::new(
            ErrorKind::InvalidData,
            format!("unexpected SMTInterpol interpolant output: {interpolants}"),
        ));
    }
    // Have to add `and` to the interpolant to make it valid smt2
    interpolants.insert_str(1, "and ");
    // Format it to `assert` call so smt2parser can handle it.
    let sequent_interpolant = get_term_from_term_string(&interpolants);
    // Interpolants will now be the arguments to the `and` term created above.
    log::debug!("----------------------------------------");
    let interpolants = match sequent_interpolant {
        smt2parser::concrete::Term::Application {
            qual_identifier: _,
            arguments,
        } => arguments
            .into_iter()
            .enumerate()
            .map(|(interpolant_number, term)| Interpolant::new(term, interpolant_number))
            .collect(),
        _ => panic!("Sequent interpolant is not `and` application."),
    };
    Ok(interpolants)
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum StatisticsValue {
    UInt(u64),
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

impl StatisticsValue {
    pub fn as_f64(&self) -> f64 {
        match self {
            StatisticsValue::UInt(int) => *int as f64,
            StatisticsValue::Double(float) => *float,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, Default)]
pub struct SolverStatistics {
    stats: BTreeMap<String, StatisticsValue>,
}

impl SolverStatistics {
    pub fn new() -> SolverStatistics {
        SolverStatistics {
            stats: BTreeMap::new(),
        }
    }

    pub(crate) fn insert(&mut self, key: String, value: StatisticsValue) {
        self.stats.insert(key, value);
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

    pub fn add_count(&mut self, key: &str, count: u64) {
        let previous = self.get_f64(key).unwrap_or(0.0);
        self.stats.insert(
            key.to_string(),
            StatisticsValue::Double(previous + count as f64),
        );
    }

    pub fn get_f64(&self, key: &str) -> Option<f64> {
        self.stats.get(key).map(StatisticsValue::as_f64)
    }

    pub fn to_json_value(&self) -> JsonValue {
        let object = self
            .stats
            .iter()
            .filter_map(|(key, value)| {
                JsonNumber::from_f64(value.as_f64())
                    .map(|number| (key.clone(), JsonValue::Number(number)))
            })
            .collect::<JsonMap<String, JsonValue>>();
        JsonValue::Object(object)
    }

    pub fn delta_since(&self, previous: &SolverStatistics) -> JsonValue {
        self.delta_snapshot_since(previous).to_json_value()
    }

    pub fn delta_snapshot_since(&self, previous: &SolverStatistics) -> SolverStatistics {
        let mut keys = self
            .stats
            .keys()
            .chain(previous.stats.keys())
            .cloned()
            .collect::<Vec<_>>();
        keys.sort();
        keys.dedup();

        let stats = keys
            .iter()
            .map(|key| {
                let current = self.get_f64(key).unwrap_or(0.0);
                let previous = previous.get_f64(key).unwrap_or(0.0);
                (key.clone(), StatisticsValue::Double(current - previous))
            })
            .collect();

        SolverStatistics { stats }
    }
}

#[cfg(test)]
mod interpolation_tests {
    use super::*;

    fn query(frames: Vec<u16>) -> SequenceInterpolationQuery {
        SequenceInterpolationQuery {
            smt2: String::new(),
            depth: 5,
            logic: "QF_AUFLIA".to_string(),
            interpolant_frames: frames,
        }
    }

    #[test]
    fn sequence_output_retains_the_explicit_partition_frame_mapping() {
        let sequence =
            parse_sequence_smtinterpol_output(query(vec![2, 4]), "unsat\n((<= i@2 0)\n (= i@4 1))")
                .unwrap();

        assert_eq!(sequence.depth, 5);
        assert_eq!(sequence.logic, "QF_AUFLIA");
        assert_eq!(
            sequence
                .partitions
                .iter()
                .map(|partition| partition.frame)
                .collect::<Vec<_>>(),
            [2, 4]
        );
        assert_eq!(sequence.predicates.candidates().len(), 2);
    }

    #[test]
    fn sequence_output_rejects_an_unexpected_interpolant_count() {
        let error = parse_sequence_smtinterpol_output(query(vec![0, 1]), "unsat\n((<= i@0 0))")
            .unwrap_err();

        assert!(error.to_string().contains("2 frame boundaries"));
    }

    #[test]
    fn interpolation_rejects_unsupported_bitvector_and_mixed_logics() {
        assert!(validate_smtinterpol_logic("QF_AUFBV").is_err());
        assert!(validate_smtinterpol_logic("ALL").is_err());
        assert!(validate_smtinterpol_logic("QF_AUFLIA").is_ok());
    }
}

#[cfg(test)]
mod solver_statistics_tests {
    use super::*;

    #[test]
    fn statistics_delta_snapshot_covers_added_changed_and_removed_keys() {
        let mut before = SolverStatistics::new();
        before.insert("changed".to_string(), StatisticsValue::UInt(3));
        before.insert("removed".to_string(), StatisticsValue::UInt(7));
        let mut after = SolverStatistics::new();
        after.insert("added".to_string(), StatisticsValue::UInt(11));
        after.insert("changed".to_string(), StatisticsValue::UInt(8));

        let delta = after.delta_snapshot_since(&before);

        assert_eq!(delta.get_f64("added"), Some(11.0));
        assert_eq!(delta.get_f64("changed"), Some(5.0));
        assert_eq!(delta.get_f64("removed"), Some(-7.0));
    }
}
