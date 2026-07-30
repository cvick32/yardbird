use std::{
    cell::RefCell,
    collections::BTreeMap,
    fs::{self, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
    rc::Rc,
    time::Duration,
};

use serde::{Deserialize, Serialize};
use smt2parser::concrete::{Command, Sort, Symbol, Term};

use crate::{profiling::ProfilingRunRecord, utils::SolverStatistics, SolverBackend};

use super::{SolverCheckResult, YardbirdSolver};

const MANIFEST_FILE: &str = "manifest.json";
const PROFILE_FILE: &str = "yardbird-profile.json";
const TRANSCRIPT_FILE: &str = "solver-session.smt2";
const INDEX_FILE: &str = "solver-session.index.json";

#[derive(Debug, Clone)]
pub struct SolverCapture {
    output_dir: PathBuf,
    state: Rc<RefCell<CaptureState>>,
}

impl SolverCapture {
    pub fn new(output_dir: impl Into<PathBuf>) -> Self {
        Self {
            output_dir: output_dir.into(),
            state: Rc::new(RefCell::new(CaptureState::default())),
        }
    }

    pub fn finish(&self, profile: &ProfilingRunRecord) -> anyhow::Result<CaptureArtifacts> {
        let (transcript, index, manifest) = {
            let state = self.state.borrow();
            if state.finished {
                anyhow::bail!("solver capture has already been finalized");
            }
            let configuration = state
                .configuration
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("solver capture was never attached to a solver"))?;
            if state.checks.is_empty() {
                anyhow::bail!("solver capture contains no solver checks");
            }
            if profile.solver_checks.len() != state.checks.len() {
                anyhow::bail!(
                    "capture observed {} checks but the Yardbird profile contains {}",
                    state.checks.len(),
                    profile.solver_checks.len()
                );
            }

            let final_transcript_end = state.transcript.len() as u64;
            let checks = state
                .checks
                .iter()
                .enumerate()
                .zip(&profile.solver_checks)
                .map(|((expected_check_id, captured), profiled)| {
                    let expected_check_id = expected_check_id as u64;
                    if captured.check_id != expected_check_id {
                        anyhow::bail!(
                            "capture check IDs are not contiguous: expected {expected_check_id}, observed {}",
                            captured.check_id
                        );
                    }
                    if captured.check_id != profiled.check_id {
                        anyhow::bail!(
                            "capture check {} does not match profile check {}",
                            captured.check_id,
                            profiled.check_id
                        );
                    }
                    if captured.expected_result != profiled.result {
                        anyhow::bail!(
                            "capture result {:?} does not match profile result {:?}",
                            captured.expected_result,
                            profiled.result
                        );
                    }
                    let completed_post_check_byte_end =
                        captured.post_check_byte_end.ok_or_else(|| {
                            anyhow::anyhow!(
                                "capture check {} was not marked complete",
                                captured.check_id
                            )
                        })?;
                    let post_check_byte_end = if expected_check_id + 1
                        == state.checks.len() as u64
                    {
                        final_transcript_end
                    } else {
                        completed_post_check_byte_end
                    };
                    if !(captured.setup_byte_start <= captured.check_byte_start
                        && captured.check_byte_start < captured.check_byte_end
                        && captured.check_byte_end <= post_check_byte_end
                        && post_check_byte_end <= final_transcript_end)
                    {
                        anyhow::bail!(
                            "capture check {} has invalid transcript boundaries",
                            captured.check_id
                        );
                    }
                    Ok(SolverSessionCheckIndex {
                        check_id: profiled.check_id,
                        depth: profiled.depth,
                        refinement_id: profiled.refinement_id,
                        refinement_step: profiled.refinement_step,
                        setup_byte_start: captured.setup_byte_start,
                        check_byte_start: captured.check_byte_start,
                        check_byte_end: captured.check_byte_end,
                        post_check_byte_end,
                        command_ordinal: captured.command_ordinal,
                        expected_result: captured.expected_result,
                    })
                })
                .collect::<anyhow::Result<Vec<_>>>()?;

            let profiled = &profile.solver_checks[0];
            for check in &profile.solver_checks {
                if configuration.backend != check.backend || configuration.logic != check.logic {
                    anyhow::bail!(
                        "captured solver configuration does not match Yardbird profile check {}",
                        check.check_id
                    );
                }
                if check.run_id != profiled.run_id
                    || check.benchmark_id != profiled.benchmark_id
                    || check.strategy != profiled.strategy
                    || check.cost_function != profiled.cost_function
                    || check.theory != profiled.theory
                {
                    anyhow::bail!(
                        "Yardbird profile check {} does not belong to the captured run",
                        check.check_id
                    );
                }
            }
            (
                state.transcript.clone(),
                SolverSessionIndex { checks },
                SolverSessionManifest {
                    complete: true,
                    run_id: profiled.run_id.clone(),
                    benchmark_id: profiled.benchmark_id.clone(),
                    strategy: profiled.strategy.clone(),
                    cost_function: profiled.cost_function.clone(),
                    theory: profiled.theory.clone(),
                    backend: configuration.backend,
                    logic: configuration.logic.clone(),
                    solver_parameters: configuration.solver_parameters.clone(),
                    random_seeds: configuration.random_seeds.clone(),
                    check_count: state.checks.len() as u64,
                    transcript: TRANSCRIPT_FILE.to_string(),
                    index: INDEX_FILE.to_string(),
                    profile: PROFILE_FILE.to_string(),
                },
            )
        };

        fs::create_dir_all(&self.output_dir)?;
        let artifacts = CaptureArtifacts::new(&self.output_dir);
        for path in artifacts.paths() {
            if path.exists() {
                anyhow::bail!("refusing to overwrite capture artifact {}", path.display());
            }
        }

        write_new(&artifacts.transcript, transcript.as_bytes())?;
        write_json(&artifacts.index, &index)?;
        write_json(&artifacts.profile, profile)?;
        write_json(&artifacts.manifest, &manifest)?;
        self.state.borrow_mut().finished = true;
        Ok(artifacts)
    }

    pub(crate) fn wrap(
        &self,
        solver: Box<dyn YardbirdSolver>,
        logic: &str,
    ) -> Box<dyn YardbirdSolver> {
        Box::new(CapturingSolver::new(solver, logic, self.clone()))
    }

    fn initialize(&self, configuration: SolverConfiguration) {
        let mut state = self.state.borrow_mut();
        assert!(
            state.configuration.is_none(),
            "solver capture cannot be attached to more than one solver"
        );
        state.append_command("(set-option :print-success false)");

        let mut options = configuration.solver_parameters.clone();
        for (name, value) in &configuration.random_seeds {
            options.insert(name.clone(), value.to_string());
        }
        for (name, value) in options {
            state.append_command(&format!(
                "(set-option :{} {})",
                smtlib_option_name(&name),
                value
            ));
        }
        state.append_command(&format!("(set-logic {})", configuration.logic));
        state.configuration = Some(configuration);
    }

    fn record_command(&self, command: impl AsRef<str>) {
        self.state.borrow_mut().append_command(command.as_ref());
    }

    fn begin_check(&self) -> (u64, u64, u64, u64, u64) {
        let mut state = self.state.borrow_mut();
        let check_id = state.checks.len() as u64;
        let setup_byte_start = state
            .checks
            .last()
            .map(|check| {
                check.post_check_byte_end.unwrap_or_else(|| {
                    panic!(
                        "solver check {} was not completed before starting check {check_id}",
                        check.check_id
                    )
                })
            })
            .unwrap_or(0);
        state.append_comment(&format!("yardbird check {check_id} begin"));
        let check_byte_start = state.transcript.len() as u64;
        let command_ordinal = state.command_ordinal;
        state.append_command("(check-sat)");
        let check_byte_end = state.transcript.len() as u64;
        (
            check_id,
            setup_byte_start,
            check_byte_start,
            check_byte_end,
            command_ordinal,
        )
    }

    fn end_check(
        &self,
        check_id: u64,
        setup_byte_start: u64,
        check_byte_start: u64,
        check_byte_end: u64,
        command_ordinal: u64,
        result: SolverCheckResult,
    ) {
        let mut state = self.state.borrow_mut();
        state.append_comment(&format!(
            "yardbird check {check_id} result {}",
            result_name(result)
        ));
        state.checks.push(CapturedCheck {
            check_id,
            setup_byte_start,
            check_byte_start,
            check_byte_end,
            post_check_byte_end: None,
            command_ordinal,
            expected_result: result,
        });
    }

    fn complete_check(&self) {
        let mut state = self.state.borrow_mut();
        let post_check_byte_end = state.transcript.len() as u64;
        let check = state
            .checks
            .last_mut()
            .expect("cannot complete a solver check before check-sat");
        assert!(
            check.post_check_byte_end.is_none(),
            "solver check {} was completed more than once",
            check.check_id
        );
        check.post_check_byte_end = Some(post_check_byte_end);
    }
}

#[derive(Debug, Clone)]
pub struct CaptureArtifacts {
    pub manifest: PathBuf,
    pub profile: PathBuf,
    pub transcript: PathBuf,
    pub index: PathBuf,
}

impl CaptureArtifacts {
    fn new(output_dir: &Path) -> Self {
        Self {
            manifest: output_dir.join(MANIFEST_FILE),
            profile: output_dir.join(PROFILE_FILE),
            transcript: output_dir.join(TRANSCRIPT_FILE),
            index: output_dir.join(INDEX_FILE),
        }
    }

    fn paths(&self) -> [&Path; 4] {
        [&self.manifest, &self.profile, &self.transcript, &self.index]
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverSessionManifest {
    pub complete: bool,
    pub run_id: String,
    pub benchmark_id: String,
    pub strategy: String,
    pub cost_function: String,
    pub theory: String,
    pub backend: SolverBackend,
    pub logic: String,
    pub solver_parameters: BTreeMap<String, String>,
    pub random_seeds: BTreeMap<String, u64>,
    pub check_count: u64,
    pub transcript: String,
    pub index: String,
    pub profile: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverSessionIndex {
    pub checks: Vec<SolverSessionCheckIndex>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverSessionCheckIndex {
    pub check_id: u64,
    pub depth: u16,
    pub refinement_id: u32,
    pub refinement_step: u32,
    pub setup_byte_start: u64,
    pub check_byte_start: u64,
    pub check_byte_end: u64,
    pub post_check_byte_end: u64,
    pub command_ordinal: u64,
    pub expected_result: SolverCheckResult,
}

#[derive(Debug, Default)]
struct CaptureState {
    transcript: String,
    command_ordinal: u64,
    checks: Vec<CapturedCheck>,
    configuration: Option<SolverConfiguration>,
    finished: bool,
}

impl CaptureState {
    fn append_command(&mut self, command: &str) {
        self.transcript.push_str(command);
        self.transcript.push('\n');
        self.command_ordinal += 1;
    }

    fn append_comment(&mut self, comment: &str) {
        self.transcript.push_str("; ");
        self.transcript.push_str(comment);
        self.transcript.push('\n');
    }
}

#[derive(Debug, Clone)]
struct SolverConfiguration {
    backend: SolverBackend,
    logic: String,
    solver_parameters: BTreeMap<String, String>,
    random_seeds: BTreeMap<String, u64>,
}

#[derive(Debug, Clone)]
struct CapturedCheck {
    check_id: u64,
    setup_byte_start: u64,
    check_byte_start: u64,
    check_byte_end: u64,
    post_check_byte_end: Option<u64>,
    command_ordinal: u64,
    expected_result: SolverCheckResult,
}

struct CapturingSolver {
    inner: Box<dyn YardbirdSolver>,
    capture: SolverCapture,
}

impl CapturingSolver {
    fn new(inner: Box<dyn YardbirdSolver>, logic: &str, capture: SolverCapture) -> Self {
        capture.initialize(SolverConfiguration {
            backend: inner.backend(),
            logic: logic.to_string(),
            solver_parameters: inner.solver_parameters(),
            random_seeds: inner.random_seeds(),
        });
        Self { inner, capture }
    }
}

impl YardbirdSolver for CapturingSolver {
    fn backend(&self) -> SolverBackend {
        self.inner.backend()
    }

    fn solver_parameters(&self) -> BTreeMap<String, String> {
        self.inner.solver_parameters()
    }

    fn random_seeds(&self) -> BTreeMap<String, u64> {
        self.inner.random_seeds()
    }

    fn accept_command(&mut self, command: &Command) -> anyhow::Result<()> {
        self.inner.accept_command(command)?;
        self.capture.record_command(command.to_string());
        Ok(())
    }

    fn create_variable(&mut self, symbol: &Symbol, sort: &Sort) -> anyhow::Result<()> {
        self.inner.create_variable(symbol, sort)
    }

    fn assert_term(&mut self, term: &Term) -> anyhow::Result<()> {
        self.inner.assert_term(term)?;
        self.capture.record_command(format!("(assert {term})"));
        Ok(())
    }

    fn assert_not_term(&mut self, term: &Term) -> anyhow::Result<()> {
        self.inner.assert_not_term(term)?;
        self.capture
            .record_command(format!("(assert (not {term}))"));
        Ok(())
    }

    fn assert_terms_conjunctively(&mut self, terms: &[Term]) -> anyhow::Result<()> {
        self.inner.assert_terms_conjunctively(terms)?;
        match terms {
            [] => {}
            [term] => self.capture.record_command(format!("(assert {term})")),
            _ => self.capture.record_command(format!(
                "(assert (and {}))",
                terms
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" ")
            )),
        }
        Ok(())
    }

    fn assert_tracked_term(&mut self, term: &Term, label: &str) -> anyhow::Result<()> {
        self.inner.assert_tracked_term(term, label)?;
        self.capture
            .record_command(format!("(assert (! {term} :named {label}))"));
        Ok(())
    }

    fn push(&mut self) {
        self.inner.push();
        self.capture.record_command("(push 1)");
    }

    fn pop(&mut self, levels: u32) {
        self.inner.pop(levels);
        self.capture.record_command(format!("(pop {levels})"));
    }

    fn check_sat(&mut self) -> SolverCheckResult {
        let (check_id, setup_byte_start, check_byte_start, check_byte_end, command_ordinal) =
            self.capture.begin_check();
        let result = self.inner.check_sat();
        self.capture.end_check(
            check_id,
            setup_byte_start,
            check_byte_start,
            check_byte_end,
            command_ordinal,
            result,
        );
        result
    }

    fn capture_model(&mut self, terms: &[Term]) -> anyhow::Result<()> {
        self.inner.capture_model(terms)
    }

    fn complete_check(&mut self) {
        self.inner.complete_check();
        self.capture.complete_check();
    }

    fn record_statistics(&mut self, solver_elapsed: Duration) {
        self.inner.record_statistics(solver_elapsed);
    }

    fn inspect_last_proof(&self) -> anyhow::Result<()> {
        self.inner.inspect_last_proof()
    }

    fn has_model(&self) -> bool {
        self.inner.has_model()
    }

    fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
        self.inner.eval_to_string(term)
    }

    fn model_to_string(&self) -> anyhow::Result<String> {
        self.inner.model_to_string()
    }

    fn get_solver_statistics(&self) -> SolverStatistics {
        self.inner.get_solver_statistics()
    }

    fn statistics_ref(&self) -> &SolverStatistics {
        self.inner.statistics_ref()
    }

    fn get_reason_unknown(&self) -> Option<String> {
        self.inner.get_reason_unknown()
    }

    fn get_unsat_core(&self) -> anyhow::Result<Vec<String>> {
        self.inner.get_unsat_core()
    }

    fn to_smt2_string(&self) -> anyhow::Result<String> {
        self.inner.to_smt2_string()
    }
}

fn write_json(path: &Path, value: &impl Serialize) -> anyhow::Result<()> {
    let mut json = serde_json::to_vec_pretty(value)?;
    json.push(b'\n');
    write_new(path, &json)
}

fn write_new(path: &Path, contents: &[u8]) -> anyhow::Result<()> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
    file.write_all(contents)?;
    Ok(())
}

fn result_name(result: SolverCheckResult) -> &'static str {
    match result {
        SolverCheckResult::Sat => "sat",
        SolverCheckResult::Unsat => "unsat",
        SolverCheckResult::Unknown => "unknown",
    }
}

fn smtlib_option_name(name: &str) -> &str {
    match name.trim_start_matches(':') {
        "random_seed" => "random-seed",
        other => other,
    }
}
