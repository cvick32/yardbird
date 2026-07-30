use std::{fs, process::Command};

use tempfile::TempDir;
use yardbird::{
    model_from_options,
    profiling::ProfilingRunRecord,
    smtlib_problem::{SMTLIBProblem, SMTLIBSolver},
    solver::{SolverCheckResult, SolverSessionIndex, SolverSessionManifest},
    Driver, SolverBackend, Strategy, YardbirdOptions,
};

#[test]
fn one_check_capture_writes_replayable_correlated_artifacts() {
    let temp = TempDir::new().unwrap();
    let capture_dir = temp.path().join("capture");
    let dump_path = temp.path().join("legacy-dump.smt2");
    let mut options = YardbirdOptions::from_filename("examples/array/array_copy.vmt".to_string());
    options.depth = 1;
    options.strategy = Strategy::Concrete;
    options.solver_capture_dir = Some(capture_dir.clone());

    let capture = options.build_solver_capture().unwrap();
    let model = model_from_options(&options);
    let mut driver = Driver::new(
        model,
        options.build_instantiation_strategy(),
        SolverBackend::Z3,
    )
    .with_tracking_options(Some(dump_path.to_string_lossy().into_owned()), false, None)
    .with_profiler(options.build_profiler())
    .with_solver_capture(Some(capture.clone()));

    let result = driver
        .check_strategy(options.depth, options.build_array_strategy())
        .unwrap();
    let artifacts = capture.finish(&result.profiling).unwrap();

    assert!(
        dump_path.exists(),
        "the existing --dump-solver path still runs"
    );
    assert_eq!(artifacts.manifest, capture_dir.join("manifest.json"));
    assert_eq!(
        artifacts.transcript,
        capture_dir.join("solver-session.smt2")
    );
    assert_eq!(
        artifacts.index,
        capture_dir.join("solver-session.index.json")
    );
    assert_eq!(artifacts.profile, capture_dir.join("yardbird-profile.json"));

    let transcript = fs::read_to_string(&artifacts.transcript).unwrap();
    let index: SolverSessionIndex =
        serde_json::from_slice(&fs::read(&artifacts.index).unwrap()).unwrap();
    let manifest_json: serde_json::Value =
        serde_json::from_slice(&fs::read(&artifacts.manifest).unwrap()).unwrap();
    let manifest: SolverSessionManifest = serde_json::from_value(manifest_json.clone()).unwrap();
    let profile: ProfilingRunRecord =
        serde_json::from_slice(&fs::read(&artifacts.profile).unwrap()).unwrap();

    assert!(manifest.complete);
    assert_eq!(manifest.check_count, 1);
    assert_eq!(manifest.run_id, profile.solver_checks[0].run_id);
    assert_eq!(manifest.backend, SolverBackend::Z3);
    assert_eq!(manifest.logic, "QF_AUFLIA");
    assert_eq!(manifest.random_seeds["smt.random_seed"], 0);
    assert!(manifest_json.get("schema_version").is_none());
    assert!(manifest_json.get("transcript_prefix_sha256").is_none());

    assert!(transcript.starts_with("(set-option :print-success false)\n"));
    assert!(transcript.contains("(set-option :random-seed 0)\n"));
    assert!(transcript.contains("(set-option :sat.random_seed 0)\n"));
    assert!(transcript.contains("(set-logic QF_AUFLIA)\n"));
    assert_in_order(
        &transcript,
        &[
            "(set-logic QF_AUFLIA)",
            "(declare-fun",
            "(assert",
            "(push 1)",
            "; yardbird check 0 begin",
            "(check-sat)",
            "; yardbird check 0 result unsat",
            "(pop 1)",
        ],
    );

    let check = &index.checks[0];
    assert_eq!(check.check_id, 0);
    assert_eq!(check.depth, 0);
    assert_eq!(check.refinement_id, 1);
    assert_eq!(check.refinement_step, 0);
    assert_eq!(check.expected_result, SolverCheckResult::Unsat);
    assert_eq!(check.setup_byte_start, 0);
    assert_eq!(
        &transcript[check.check_byte_start as usize..check.check_byte_end as usize],
        "(check-sat)\n"
    );
    assert_eq!(check.post_check_byte_end, transcript.len() as u64);

    let replay_problem = SMTLIBProblem::from_path(&artifacts.transcript).unwrap();
    let mut replay =
        SMTLIBSolver::new_with_backend(replay_problem.get_logic(), SolverBackend::Z3, None);
    replay.execute(&replay_problem).unwrap();
    assert_eq!(replay.get_results().len(), 1);
    assert_eq!(replay.get_results()[0].result, SolverCheckResult::Unsat);

    if let Ok(output) = Command::new("z3")
        .arg("-smt2")
        .arg(&artifacts.transcript)
        .output()
    {
        assert!(
            output.status.success(),
            "external Z3 replay failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "unsat");
    }
}

#[test]
fn abstract_capture_declares_each_uninterpreted_function_once() {
    let temp = TempDir::new().unwrap();
    let mut options = YardbirdOptions::from_filename("examples/array/array_copy.vmt".to_string());
    options.depth = 1;
    options.strategy = Strategy::Abstract;
    options.solver_capture_dir = Some(temp.path().join("capture"));

    let capture = options.build_solver_capture().unwrap();
    let mut driver = Driver::new(
        model_from_options(&options),
        options.build_instantiation_strategy(),
        SolverBackend::Z3,
    )
    .with_profiler(options.build_profiler())
    .with_solver_capture(Some(capture.clone()));
    let result = driver
        .check_strategy(options.depth, options.build_array_strategy())
        .unwrap();
    let artifacts = capture.finish(&result.profiling).unwrap();
    let transcript = fs::read_to_string(&artifacts.transcript).unwrap();

    assert_eq!(transcript.matches("(declare-fun Read_Int_Int ").count(), 1);
    assert_eq!(transcript.matches("(declare-fun Write_Int_Int ").count(), 1);
    assert_eq!(
        transcript.matches("(declare-fun ConstArr_Int_Int ").count(),
        1
    );

    let replay_problem = SMTLIBProblem::from_path(&artifacts.transcript).unwrap();
    let mut replay =
        SMTLIBSolver::new_with_backend(replay_problem.get_logic(), SolverBackend::Z3, None);
    replay.execute(&replay_problem).unwrap();
    assert_eq!(replay.get_results()[0].result, SolverCheckResult::Unsat);
}

#[test]
fn single_check_capture_rejects_an_incremental_session_without_writing_artifacts() {
    let temp = TempDir::new().unwrap();
    let capture_dir = temp.path().join("capture");
    let mut options =
        YardbirdOptions::from_filename("examples/smtlib/incremental.smt2".to_string());
    options.solver_capture_dir = Some(capture_dir.clone());
    options.strategy = Strategy::Concrete;
    let capture = options.build_solver_capture().unwrap();
    let problem = SMTLIBProblem::from_path(options.require_filename().unwrap()).unwrap();
    let mut solver = SMTLIBSolver::new_with_backend(
        problem.get_logic(),
        SolverBackend::Z3,
        Some(capture.clone()),
    )
    .with_profiler(options.build_profiler());

    solver.execute(&problem).unwrap();
    let error = capture.finish(&solver.profiling()).unwrap_err();

    assert!(error
        .to_string()
        .contains("single-check capture requires exactly one solver check"));
    assert!(!capture_dir.exists());
}

fn assert_in_order(haystack: &str, needles: &[&str]) {
    let mut cursor = 0;
    for needle in needles {
        let offset = haystack[cursor..]
            .find(needle)
            .unwrap_or_else(|| panic!("missing {needle:?} after byte {cursor}"));
        cursor += offset + needle.len();
    }
}
