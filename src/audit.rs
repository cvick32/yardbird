use std::{
    fs,
    io::{Read, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc, Arc,
    },
    thread,
    time::{Duration, Instant},
};

use anyhow::Context;
use log::info;
use smt2parser::vmt::{VMTError, VMTModel};

use crate::ProofLoopResult;

#[derive(Clone, Debug)]
pub struct AuditConfig {
    pub input: PathBuf,
    pub depth: u16,
    pub timeout: Duration,
    pub jobs: usize,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum AuditStrategy {
    Concrete,
    Abstract,
}

impl AuditStrategy {
    const ALL: [Self; 2] = [Self::Concrete, Self::Abstract];

    fn as_str(self) -> &'static str {
        match self {
            Self::Concrete => "concrete",
            Self::Abstract => "abstract",
        }
    }
}

#[derive(Debug)]
enum AuditRunOutcome {
    Completed,
    Counterexample,
    NoProgress,
    RefinementLimit,
    Timeout,
    Panic(String),
    Error(String),
    InvalidOutput(String),
}

impl AuditRunOutcome {
    fn label(&self) -> &'static str {
        match self {
            Self::Completed => "COMPLETED",
            Self::Counterexample => "COUNTEREXAMPLE",
            Self::NoProgress => "NO_PROGRESS",
            Self::RefinementLimit => "REFINEMENT_LIMIT",
            Self::Timeout => "TIMEOUT",
            Self::Panic(_) => "PANIC",
            Self::Error(_) => "ERROR",
            Self::InvalidOutput(_) => "INVALID_OUTPUT",
        }
    }

    fn detail(&self) -> &str {
        match self {
            Self::Panic(detail) | Self::Error(detail) | Self::InvalidOutput(detail) => detail,
            _ => "",
        }
    }
}

#[derive(Debug)]
struct AuditRecord {
    path: PathBuf,
    strategy: AuditStrategy,
    elapsed: Duration,
    outcome: AuditRunOutcome,
}

#[derive(Debug)]
struct ParseFailure {
    path: PathBuf,
    label: &'static str,
    detail: String,
}

#[derive(Debug)]
struct ParseRecord {
    path: PathBuf,
    failure: Option<ParseFailure>,
}

#[derive(Default)]
struct StrategyCounts {
    completed: usize,
    counterexamples: usize,
    no_progress: usize,
    refinement_limits: usize,
    timeouts: usize,
    panics: usize,
    errors: usize,
    invalid_output: usize,
}

impl StrategyCounts {
    fn add(&mut self, outcome: &AuditRunOutcome) {
        match outcome {
            AuditRunOutcome::Completed => self.completed += 1,
            AuditRunOutcome::Counterexample => self.counterexamples += 1,
            AuditRunOutcome::NoProgress => self.no_progress += 1,
            AuditRunOutcome::RefinementLimit => self.refinement_limits += 1,
            AuditRunOutcome::Timeout => self.timeouts += 1,
            AuditRunOutcome::Panic(_) => self.panics += 1,
            AuditRunOutcome::Error(_) => self.errors += 1,
            AuditRunOutcome::InvalidOutput(_) => self.invalid_output += 1,
        }
    }
}

#[derive(Debug)]
pub struct AuditReport {
    files: usize,
    parsed: usize,
    parse_failures: Vec<ParseFailure>,
    records: Vec<AuditRecord>,
    elapsed: Duration,
}

impl AuditReport {
    pub fn write_tsv(&self, mut writer: impl Write) -> std::io::Result<()> {
        writeln!(writer, "status\tstrategy\telapsed_ms\tpath\tdetail")?;
        for failure in &self.parse_failures {
            writeln!(
                writer,
                "{}\t-\t0\t{}\t{}",
                failure.label,
                clean_field(&failure.path.display().to_string()),
                clean_field(&failure.detail)
            )?;
        }
        for record in &self.records {
            writeln!(
                writer,
                "{}\t{}\t{}\t{}\t{}",
                record.outcome.label(),
                record.strategy.as_str(),
                record.elapsed.as_millis(),
                clean_field(&record.path.display().to_string()),
                clean_field(record.outcome.detail())
            )?;
        }

        writeln!(
            writer,
            "SUMMARY\tall\t{}\tfiles={}\tparsed={} parse_failures={} runs={}",
            self.elapsed.as_millis(),
            self.files,
            self.parsed,
            self.parse_failures.len(),
            self.records.len()
        )?;
        for strategy in AuditStrategy::ALL {
            let mut counts = StrategyCounts::default();
            for record in self
                .records
                .iter()
                .filter(|record| record.strategy == strategy)
            {
                counts.add(&record.outcome);
            }
            writeln!(
                writer,
                "SUMMARY\t{}\t0\t-\tcompleted={} counterexamples={} no_progress={} refinement_limits={} timeouts={} panics={} errors={} invalid_output={}",
                strategy.as_str(),
                counts.completed,
                counts.counterexamples,
                counts.no_progress,
                counts.refinement_limits,
                counts.timeouts,
                counts.panics,
                counts.errors,
                counts.invalid_output
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct AuditTask {
    path: PathBuf,
    strategy: AuditStrategy,
}

pub fn run(config: AuditConfig) -> anyhow::Result<AuditReport> {
    anyhow::ensure!(config.jobs > 0, "audit jobs must be greater than zero");
    anyhow::ensure!(
        !config.timeout.is_zero(),
        "audit timeout must be greater than zero"
    );

    let started = Instant::now();
    let mut files = Vec::new();
    collect_vmt_files(&config.input, &mut files)?;
    files.sort();

    info!(
        "Audit discovered {} VMT files; parsing before {} isolated runs per parsed file",
        files.len(),
        AuditStrategy::ALL.len()
    );

    let executable = std::env::current_exe().context("failed to locate the Yardbird executable")?;
    let (parsed, parse_failures) = preflight_files(&files, &executable, &config)?;

    let tasks = parsed
        .iter()
        .flat_map(|path| {
            AuditStrategy::ALL
                .into_iter()
                .map(move |strategy| AuditTask {
                    path: path.clone(),
                    strategy,
                })
        })
        .collect::<Vec<_>>();
    let records = run_tasks(tasks, executable, &config)?;

    Ok(AuditReport {
        files: files.len(),
        parsed: parsed.len(),
        parse_failures,
        records,
        elapsed: started.elapsed(),
    })
}

/// Parse one VMT in an isolated audit worker process.
///
/// The marker prefixes let the parent distinguish grammar failures from VMT
/// model-validation failures without exposing a second machine-readable format.
pub fn parse_only(path: &Path) -> anyhow::Result<()> {
    match VMTModel::from_path(path) {
        Ok(_) => Ok(()),
        Err(VMTError::VisitorError(error)) => {
            anyhow::bail!("[AUDIT_SYNTAX_ERROR] {error}")
        }
        Err(error) => anyhow::bail!("[AUDIT_VMT_ERROR] {error}"),
    }
}

fn preflight_files(
    files: &[PathBuf],
    executable: &Path,
    config: &AuditConfig,
) -> anyhow::Result<(Vec<PathBuf>, Vec<ParseFailure>)> {
    if files.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }

    let files = Arc::new(files.to_vec());
    let next_file = Arc::new(AtomicUsize::new(0));
    let (sender, receiver) = mpsc::channel();
    let worker_count = config.jobs.min(files.len());
    let mut workers = Vec::with_capacity(worker_count);

    for _ in 0..worker_count {
        let files = Arc::clone(&files);
        let next_file = Arc::clone(&next_file);
        let sender = sender.clone();
        let executable = executable.to_path_buf();
        let timeout = config.timeout;
        workers.push(thread::spawn(move || loop {
            let index = next_file.fetch_add(1, Ordering::Relaxed);
            let Some(path) = files.get(index) else {
                break;
            };
            if sender
                .send(run_parse_task(path, &executable, timeout))
                .is_err()
            {
                break;
            }
        }));
    }
    drop(sender);

    let mut parsed = Vec::new();
    let mut failures = Vec::new();
    for record in receiver {
        match record.failure {
            Some(failure) => failures.push(failure),
            None => parsed.push(record.path),
        }
    }
    for worker in workers {
        worker
            .join()
            .map_err(|_| anyhow::anyhow!("an audit parser worker thread panicked"))?;
    }
    parsed.sort();
    failures.sort_by(|left, right| left.path.cmp(&right.path));
    Ok((parsed, failures))
}

fn run_parse_task(path: &Path, executable: &Path, timeout: Duration) -> ParseRecord {
    let failure = (|| -> anyhow::Result<Option<ParseFailure>> {
        let input = fs::canonicalize(path)
            .with_context(|| format!("failed to resolve {}", path.display()))?;
        let mut command = Command::new(executable);
        command
            .arg("__audit-parse")
            .arg(input)
            .env("RUST_LOG", "error")
            .env("RUST_BACKTRACE", "0");
        let output = run_command(command, timeout)?;
        if output.timed_out {
            return Ok(Some(ParseFailure {
                path: path.to_path_buf(),
                label: "PARSE_TIMEOUT",
                detail: String::new(),
            }));
        }
        if output.success {
            return Ok(None);
        }

        let lower = output.stderr.to_ascii_lowercase();
        let label = if lower.contains("[audit_syntax_error]") {
            "SYNTAX_ERROR"
        } else if lower.contains("[audit_vmt_error]") {
            "VMT_ERROR"
        } else if lower.contains("panicked at")
            || lower.contains("not yet implemented")
            || lower.contains("fatal runtime error")
        {
            "PARSE_PANIC"
        } else {
            "PARSE_ERROR"
        };
        Ok(Some(ParseFailure {
            path: path.to_path_buf(),
            label,
            detail: diagnostic(&output.stderr),
        }))
    })()
    .unwrap_or_else(|error| {
        Some(ParseFailure {
            path: path.to_path_buf(),
            label: "PARSE_ERROR",
            detail: format!("{error:#}"),
        })
    });

    ParseRecord {
        path: path.to_path_buf(),
        failure,
    }
}

fn run_tasks(
    tasks: Vec<AuditTask>,
    executable: PathBuf,
    config: &AuditConfig,
) -> anyhow::Result<Vec<AuditRecord>> {
    if tasks.is_empty() {
        return Ok(Vec::new());
    }

    let tasks = Arc::new(tasks);
    let next_task = Arc::new(AtomicUsize::new(0));
    let (sender, receiver) = mpsc::channel();
    let worker_count = config.jobs.min(tasks.len());
    let mut workers = Vec::with_capacity(worker_count);

    for _ in 0..worker_count {
        let tasks = Arc::clone(&tasks);
        let next_task = Arc::clone(&next_task);
        let sender = sender.clone();
        let executable = executable.clone();
        let timeout = config.timeout;
        let depth = config.depth;
        workers.push(thread::spawn(move || loop {
            let index = next_task.fetch_add(1, Ordering::Relaxed);
            let Some(task) = tasks.get(index) else {
                break;
            };
            if sender
                .send(run_task(task, &executable, depth, timeout))
                .is_err()
            {
                break;
            }
        }));
    }
    drop(sender);

    let total = tasks.len();
    let mut records = Vec::with_capacity(total);
    for record in receiver {
        records.push(record);
        if records.len() % 100 == 0 || records.len() == total {
            info!("Audit completed {}/{} Yardbird runs", records.len(), total);
        }
    }
    for worker in workers {
        worker
            .join()
            .map_err(|_| anyhow::anyhow!("an audit worker thread panicked"))?;
    }

    records.sort_by(|left, right| {
        left.path
            .cmp(&right.path)
            .then(left.strategy.cmp(&right.strategy))
    });
    Ok(records)
}

fn run_task(task: &AuditTask, executable: &Path, depth: u16, timeout: Duration) -> AuditRecord {
    let started = Instant::now();
    let outcome = (|| -> anyhow::Result<AuditRunOutcome> {
        let input = fs::canonicalize(&task.path)
            .with_context(|| format!("failed to resolve {}", task.path.display()))?;
        let working_directory = tempfile::tempdir().context("failed to create audit workdir")?;
        let mut command = Command::new(executable);
        command
            .arg("--filename")
            .arg(input)
            .arg("--depth")
            .arg(depth.to_string())
            .arg("--strategy")
            .arg(task.strategy.as_str())
            .arg("--json-output")
            .current_dir(working_directory.path())
            .env("RUST_LOG", "error")
            .env("RUST_BACKTRACE", "0");

        let output = run_command(command, timeout)?;
        if output.timed_out {
            Ok(AuditRunOutcome::Timeout)
        } else {
            Ok(classify_output(
                output.success,
                &output.stdout,
                &output.stderr,
            ))
        }
    })()
    .unwrap_or_else(|error| AuditRunOutcome::Error(format!("{error:#}")));

    AuditRecord {
        path: task.path.clone(),
        strategy: task.strategy,
        elapsed: started.elapsed(),
        outcome,
    }
}

struct ProcessOutput {
    success: bool,
    timed_out: bool,
    stdout: String,
    stderr: String,
}

fn run_command(mut command: Command, timeout: Duration) -> std::io::Result<ProcessOutput> {
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let stdout_reader = child.stdout.take().map(read_pipe_in_background);
    let stderr_reader = child.stderr.take().map(read_pipe_in_background);
    let started = Instant::now();

    let (success, timed_out) = loop {
        match child.try_wait()? {
            Some(status) => break (status.success(), false),
            None if started.elapsed() >= timeout => {
                let _ = child.kill();
                let status = child.wait()?;
                break (status.success(), true);
            }
            None => thread::sleep(Duration::from_millis(10)),
        }
    };

    Ok(ProcessOutput {
        success,
        timed_out,
        stdout: collect_reader(stdout_reader),
        stderr: collect_reader(stderr_reader),
    })
}

fn read_pipe_in_background<R>(mut pipe: R) -> thread::JoinHandle<String>
where
    R: Read + Send + 'static,
{
    thread::spawn(move || {
        let mut output = String::new();
        let _ = pipe.read_to_string(&mut output);
        output
    })
}

fn collect_reader(reader: Option<thread::JoinHandle<String>>) -> String {
    reader
        .and_then(|reader| reader.join().ok())
        .unwrap_or_default()
}

fn classify_output(success: bool, stdout: &str, stderr: &str) -> AuditRunOutcome {
    if success {
        return match serde_json::from_str::<ProofLoopResult>(stdout.trim()) {
            Ok(result) if result.counterexample => AuditRunOutcome::Counterexample,
            Ok(_) => AuditRunOutcome::Completed,
            Err(error) => AuditRunOutcome::InvalidOutput(format!(
                "failed to parse Yardbird JSON: {error}; stdout={}",
                diagnostic(stdout)
            )),
        };
    }

    let lower = stderr.to_ascii_lowercase();
    if lower.contains("panicked at")
        || lower.contains("not yet implemented")
        || lower.contains("fatal runtime error")
    {
        AuditRunOutcome::Panic(diagnostic(stderr))
    } else if lower.contains("counter-example") || lower.contains("counterexample") {
        AuditRunOutcome::Counterexample
    } else if lower.contains("no progress") {
        AuditRunOutcome::NoProgress
    } else if lower.contains("refinement limit") || lower.contains("too many refinements") {
        AuditRunOutcome::RefinementLimit
    } else {
        AuditRunOutcome::Error(diagnostic(stderr))
    }
}

fn diagnostic(output: &str) -> String {
    let lines = output.lines().collect::<Vec<_>>();
    let preferred = lines
        .iter()
        .position(|line| line.contains("panicked at"))
        .map(|index| {
            let location = lines[index].trim();
            let message = lines
                .iter()
                .skip(index + 1)
                .find(|line| !line.trim().is_empty())
                .map(|line| line.trim());
            match message {
                Some(message) => format!("{location} {message}"),
                None => location.to_string(),
            }
        })
        .or_else(|| {
            lines
                .iter()
                .find(|line| line.starts_with("Error:"))
                .map(|line| (*line).to_string())
        })
        .or_else(|| {
            lines
                .iter()
                .rev()
                .find(|line| !line.trim().is_empty())
                .map(|line| (*line).to_string())
        })
        .unwrap_or_else(|| "process exited without a diagnostic".to_string());
    preferred.chars().take(500).collect()
}

fn collect_vmt_files(path: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if path.is_file() {
        if path
            .extension()
            .and_then(|extension| extension.to_str())
            .is_some_and(|extension| extension.eq_ignore_ascii_case("vmt"))
        {
            files.push(path.to_path_buf());
        }
        return Ok(());
    }

    if !path.is_dir() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("audit input does not exist: {}", path.display()),
        ));
    }

    let mut entries = fs::read_dir(path)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|entry| entry.path());
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() || file_type.is_file() {
            collect_vmt_files(&path, files)?;
        }
    }
    Ok(())
}

fn clean_field(value: &str) -> String {
    value.replace(['\t', '\n', '\r'], " ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::Parser;

    use crate::{YardbirdCommand, YardbirdOptions};

    #[test]
    fn audit_cli_defaults_to_requested_smoke_test_limits() {
        let options = YardbirdOptions::try_parse_from(["yardbird", "audit", "benchmarks"])
            .expect("audit command should parse");

        match options.command {
            Some(YardbirdCommand::Audit {
                input,
                depth,
                timeout_seconds,
                jobs,
            }) => {
                assert_eq!(input, PathBuf::from("benchmarks"));
                assert_eq!(depth, 1);
                assert_eq!(timeout_seconds, 1);
                assert_eq!(jobs, 4);
            }
            command => panic!("unexpected command: {command:?}"),
        }
    }

    #[test]
    fn parse_probe_accepts_a_repository_vmt() {
        parse_only(Path::new("examples/array/array_copy.vmt")).unwrap();
    }

    #[test]
    fn recursively_collects_only_vmt_files_in_stable_order() {
        let root = tempfile::tempdir().unwrap();
        let nested = root.path().join("nested");
        fs::create_dir(&nested).unwrap();
        fs::write(root.path().join("b.vmt"), "").unwrap();
        fs::write(root.path().join("ignored.smt2"), "").unwrap();
        fs::write(nested.join("a.VMT"), "").unwrap();

        let mut files = Vec::new();
        collect_vmt_files(root.path(), &mut files).unwrap();
        files.sort();

        assert_eq!(files, vec![root.path().join("b.vmt"), nested.join("a.VMT")]);
    }

    #[test]
    fn classifies_successful_json_and_common_failure_modes() {
        let success = serde_json::to_string(&ProofLoopResult::default()).unwrap();
        assert!(matches!(
            classify_output(true, &success, ""),
            AuditRunOutcome::Completed
        ));
        let panic = classify_output(
            false,
            "",
            "thread 'main' panicked at source.rs:1:\nunsupported operator: bvadd",
        );
        assert!(matches!(
            panic,
            AuditRunOutcome::Panic(detail) if detail.contains("unsupported operator: bvadd")
        ));
        assert!(matches!(
            classify_output(false, "", "Error: Found a counter-example"),
            AuditRunOutcome::Counterexample
        ));
        assert!(matches!(
            classify_output(false, "", "Error: Hit refinement limit of 250"),
            AuditRunOutcome::RefinementLimit
        ));
    }

    #[cfg(unix)]
    #[test]
    fn kills_a_subprocess_at_the_deadline() {
        let mut command = Command::new("/bin/sh");
        command.args(["-c", "sleep 1"]);

        let output = run_command(command, Duration::from_millis(20)).unwrap();

        assert!(output.timed_out);
    }
}
