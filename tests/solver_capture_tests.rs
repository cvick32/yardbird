use std::{fs, process::Command};

use tempfile::TempDir;
use yardbird::{
    cost_functions::array::ArrayBMCCost,
    model_from_options,
    profiling::ProfilingRunRecord,
    smtlib_problem::{SMTLIBProblem, SmtlibCommandExecutor, SmtlibRefinementRunner},
    solver::{PropertyCheckMode, SolverCheckResult, SolverSessionIndex, SolverSessionManifest},
    strategies::{Abstract, ProofStrategy},
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
    assert_valid_check_boundaries(&transcript, &index);

    let replay_problem = SMTLIBProblem::from_path(&artifacts.transcript).unwrap();
    let mut replay = SmtlibCommandExecutor::new_with_backend(
        replay_problem.get_logic(),
        SolverBackend::Z3,
        None,
    )
    .unwrap();
    replay.execute(&replay_problem).unwrap();
    assert_eq!(replay.get_results().len(), 1);
    assert_eq!(replay.get_results()[0].result, SolverCheckResult::Unsat);

    if let Ok(output) = Command::new("z3")
        .arg("-smt2")
        .arg(&artifacts.transcript)
        .current_dir(temp.path())
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
fn nonlinear_concrete_capture_uses_a_replayable_array_logic() {
    let temp = TempDir::new().unwrap();
    let capture_dir = temp.path().join("capture");
    let mut options =
        YardbirdOptions::from_filename("examples/array/array_tiling_poly1.vmt".to_string());
    options.depth = 1;
    options.strategy = Strategy::Concrete;
    options.solver_capture_dir = Some(capture_dir);

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
    let manifest: SolverSessionManifest =
        serde_json::from_slice(&fs::read(&artifacts.manifest).unwrap()).unwrap();
    let transcript = fs::read_to_string(&artifacts.transcript).unwrap();

    assert_eq!(manifest.logic, "QF_AUFNIA");
    assert!(transcript.contains("(set-logic QF_AUFNIA)\n"));
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
    let mut replay = SmtlibCommandExecutor::new_with_backend(
        replay_problem.get_logic(),
        SolverBackend::Z3,
        None,
    )
    .unwrap();
    replay.execute(&replay_problem).unwrap();
    assert_eq!(replay.get_results()[0].result, SolverCheckResult::Unsat);
}

#[test]
fn incremental_capture_preserves_every_check_and_ordered_result() {
    let temp = TempDir::new().unwrap();
    let capture_dir = temp.path().join("capture");
    let mut options =
        YardbirdOptions::from_filename("examples/smtlib/incremental.smt2".to_string());
    options.solver_capture_dir = Some(capture_dir.clone());
    options.strategy = Strategy::Concrete;
    let capture = options.build_solver_capture().unwrap();
    let problem = SMTLIBProblem::from_path(options.require_filename().unwrap()).unwrap();
    let mut solver = SmtlibCommandExecutor::new_with_backend(
        problem.get_logic(),
        SolverBackend::Z3,
        Some(capture.clone()),
    )
    .unwrap()
    .with_profiler(options.build_profiler());

    solver.execute(&problem).unwrap();
    let expected_results = solver
        .get_results()
        .iter()
        .map(|check| check.result)
        .collect::<Vec<_>>();
    let artifacts = capture.finish(&solver.profiling()).unwrap();
    let transcript = fs::read_to_string(&artifacts.transcript).unwrap();
    let index: SolverSessionIndex =
        serde_json::from_slice(&fs::read(&artifacts.index).unwrap()).unwrap();
    let manifest: SolverSessionManifest =
        serde_json::from_slice(&fs::read(&artifacts.manifest).unwrap()).unwrap();

    assert_eq!(
        expected_results,
        vec![
            SolverCheckResult::Sat,
            SolverCheckResult::Sat,
            SolverCheckResult::Unsat,
            SolverCheckResult::Sat,
            SolverCheckResult::Sat,
        ]
    );
    assert_eq!(manifest.check_count, 5);
    assert_eq!(index.checks.len(), expected_results.len());
    assert_valid_check_boundaries(&transcript, &index);
    assert_eq!(
        index
            .checks
            .iter()
            .map(|check| check.expected_result)
            .collect::<Vec<_>>(),
        expected_results
    );

    let second_setup = setup_slice(&transcript, &index, 1);
    assert!(second_setup.contains("(push 1)\n"));
    assert!(second_setup.contains("(assert (> x 5))\n"));
    let fourth_setup = setup_slice(&transcript, &index, 3);
    assert!(fourth_setup.contains("(pop 1)\n"));

    assert_eq!(
        replay_with_yardbird(&artifacts.transcript),
        expected_results
    );
    if let Some(results) = replay_with_external_z3(&artifacts.transcript) {
        assert_eq!(results, expected_results);
    }
}

#[test]
fn property_assumption_capture_is_replayable_without_property_scopes() {
    let temp = TempDir::new().unwrap();
    let capture_dir = temp.path().join("capture");
    let mut options = YardbirdOptions::from_filename(
        "examples/distributed_protocols/german/german.vmt".to_string(),
    );
    options.depth = 2;
    options.property_check_mode = PropertyCheckMode::Assumptions;
    options.solver_capture_dir = Some(capture_dir);

    let capture = options.build_solver_capture().unwrap();
    let model = model_from_options(&options);
    let mut driver = Driver::new(
        model,
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
    let index: SolverSessionIndex =
        serde_json::from_slice(&fs::read(&artifacts.index).unwrap()).unwrap();

    assert!(transcript.contains("(declare-fun yardbird_property_depth_0 () Bool)"));
    assert!(transcript.contains("(declare-fun yardbird_property_depth_1 () Bool)"));
    assert!(transcript.contains("(assert (=> yardbird_property_depth_0 (not"));
    assert!(transcript.contains("(check-sat-assuming (yardbird_property_depth_0))"));
    assert!(!transcript.contains("(push 1)"));
    assert!(!transcript.contains("(pop 1)"));
    assert_valid_check_boundaries(&transcript, &index);
    for check in &index.checks {
        assert_eq!(
            &transcript[check.check_byte_start as usize..check.check_byte_end as usize],
            format!(
                "(check-sat-assuming (yardbird_property_depth_{}))\n",
                check.depth
            )
        );
    }
    assert_eq!(
        replay_with_yardbird(&artifacts.transcript),
        index
            .checks
            .iter()
            .map(|check| check.expected_result)
            .collect::<Vec<_>>()
    );
}

#[test]
fn refinement_assumptions_switch_after_the_first_sat_check_at_each_depth() {
    let temp = TempDir::new().unwrap();
    let capture_dir = temp.path().join("capture");
    let mut options = YardbirdOptions::from_filename(
        "examples/distributed_protocols/german/german.vmt".to_string(),
    );
    options.depth = 2;
    options.property_check_mode = PropertyCheckMode::RefinementAssumptions;
    options.solver_capture_dir = Some(capture_dir);

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
    let index: SolverSessionIndex =
        serde_json::from_slice(&fs::read(&artifacts.index).unwrap()).unwrap();

    assert!(transcript.contains("(declare-fun yardbird_property_depth_0 () Bool)"));
    assert!(transcript.contains("(declare-fun yardbird_property_depth_1 () Bool)"));
    assert_valid_check_boundaries(&transcript, &index);
    for check in &index.checks {
        let captured = &transcript[check.check_byte_start as usize..check.check_byte_end as usize];
        if check.refinement_step == 0 {
            assert_eq!(captured, "(check-sat)\n");
        } else {
            assert_eq!(
                captured,
                format!(
                    "(check-sat-assuming (yardbird_property_depth_{}))\n",
                    check.depth
                )
            );
        }
    }
    assert_eq!(
        replay_with_yardbird(&artifacts.transcript),
        index
            .checks
            .iter()
            .map(|check| check.expected_result)
            .collect::<Vec<_>>()
    );
}

#[test]
fn multi_depth_capture_correlates_each_bmc_check() {
    let temp = TempDir::new().unwrap();
    let mut options = YardbirdOptions::from_filename("examples/array/array_copy.vmt".to_string());
    options.depth = 2;
    options.strategy = Strategy::Concrete;
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
    let index: SolverSessionIndex =
        serde_json::from_slice(&fs::read(&artifacts.index).unwrap()).unwrap();

    assert_eq!(index.checks.len(), 2);
    assert_eq!(
        index
            .checks
            .iter()
            .map(|check| (check.depth, check.refinement_step, check.expected_result))
            .collect::<Vec<_>>(),
        vec![
            (0, 0, SolverCheckResult::Unsat),
            (1, 0, SolverCheckResult::Unsat),
        ]
    );
    assert_valid_check_boundaries(&transcript, &index);
    for check in &index.checks {
        let post_check =
            &transcript[check.check_byte_end as usize..check.post_check_byte_end as usize];
        assert!(post_check.contains("(pop 1)\n"));
    }
    assert!(setup_slice(&transcript, &index, 1).contains("(assert"));
    assert_eq!(
        replay_with_yardbird(&artifacts.transcript),
        vec![SolverCheckResult::Unsat, SolverCheckResult::Unsat]
    );
}

#[test]
fn multi_refinement_capture_preserves_added_instances_between_checks() {
    let temp = TempDir::new().unwrap();
    let mut options =
        YardbirdOptions::from_filename("examples/smt2/array_bitvec_simple.smt2".to_string());
    options.strategy = Strategy::Abstract;
    options.solver_capture_dir = Some(temp.path().join("capture"));
    let capture = options.build_solver_capture().unwrap();
    let problem = SMTLIBProblem::from_path(options.require_filename().unwrap()).unwrap();
    let strategy: Box<dyn ProofStrategy<_>> =
        Box::new(Abstract::<ArrayBMCCost>::new(0, false, (), false));

    let result = SmtlibRefinementRunner::execute(
        &problem,
        strategy,
        SolverBackend::Z3,
        5,
        false,
        options.build_profiler(),
        Some(capture.clone()),
    )
    .unwrap()
    .0;
    let artifacts = capture.finish(&result.profiling).unwrap();
    let transcript = fs::read_to_string(&artifacts.transcript).unwrap();
    let index: SolverSessionIndex =
        serde_json::from_slice(&fs::read(&artifacts.index).unwrap()).unwrap();

    assert_eq!(
        index
            .checks
            .iter()
            .map(|check| {
                (
                    check.check_id,
                    check.depth,
                    check.refinement_step,
                    check.expected_result,
                )
            })
            .collect::<Vec<_>>(),
        vec![
            (0, 0, 0, SolverCheckResult::Sat),
            (1, 0, 1, SolverCheckResult::Unsat),
        ]
    );
    assert_valid_check_boundaries(&transcript, &index);
    let refinement_setup = setup_slice(&transcript, &index, 1);
    assert!(refinement_setup.contains("(assert"));
    assert!(refinement_setup.contains("Read_BitVec5_BitVec32"));
    assert!(refinement_setup.contains("Write_BitVec5_BitVec32"));
    assert_eq!(
        replay_with_yardbird(&artifacts.transcript),
        vec![SolverCheckResult::Sat, SolverCheckResult::Unsat]
    );
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

fn assert_valid_check_boundaries(transcript: &str, index: &SolverSessionIndex) {
    let mut prior_post_check_end = 0;
    let mut prior_command_ordinal = None;
    for (expected_id, check) in index.checks.iter().enumerate() {
        assert_eq!(check.check_id, expected_id as u64);
        assert_eq!(check.setup_byte_start, prior_post_check_end);
        assert!(check.setup_byte_start <= check.check_byte_start);
        assert!(check.check_byte_start < check.check_byte_end);
        assert!(check.check_byte_end <= check.post_check_byte_end);
        assert!(check.post_check_byte_end <= transcript.len() as u64);
        let check_command =
            &transcript[check.check_byte_start as usize..check.check_byte_end as usize];
        assert!(
            check_command == "(check-sat)\n"
                || check_command.starts_with("(check-sat-assuming (")
                    && check_command.ends_with("))\n"),
            "unexpected captured check command: {check_command:?}"
        );
        assert!(
            transcript[check.check_byte_end as usize..check.post_check_byte_end as usize].contains(
                &format!(
                    "; yardbird check {} result {}",
                    check.check_id,
                    result_name(check.expected_result)
                )
            )
        );
        if let Some(prior) = prior_command_ordinal {
            assert!(check.command_ordinal > prior);
        }
        prior_command_ordinal = Some(check.command_ordinal);
        prior_post_check_end = check.post_check_byte_end;
    }
    assert_eq!(prior_post_check_end, transcript.len() as u64);
}

fn setup_slice<'a>(transcript: &'a str, index: &SolverSessionIndex, check_id: usize) -> &'a str {
    let check = &index.checks[check_id];
    &transcript[check.setup_byte_start as usize..check.check_byte_start as usize]
}

fn replay_with_yardbird(path: &std::path::Path) -> Vec<SolverCheckResult> {
    let problem = SMTLIBProblem::from_path(path).unwrap();
    let mut replay =
        SmtlibCommandExecutor::new_with_backend(problem.get_logic(), SolverBackend::Z3, None)
            .unwrap();
    replay.execute(&problem).unwrap();
    replay
        .get_results()
        .iter()
        .map(|check| check.result)
        .collect()
}

fn replay_with_external_z3(path: &std::path::Path) -> Option<Vec<SolverCheckResult>> {
    let output = Command::new("z3")
        .arg("-smt2")
        .arg(path)
        .current_dir(path.parent().unwrap())
        .output()
        .ok()?;
    assert!(
        output.status.success(),
        "external Z3 replay failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    Some(
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(|result| match result.trim() {
                "sat" => SolverCheckResult::Sat,
                "unsat" => SolverCheckResult::Unsat,
                "unknown" => SolverCheckResult::Unknown,
                unexpected => panic!("unexpected external Z3 result {unexpected:?}"),
            })
            .collect(),
    )
}

fn result_name(result: SolverCheckResult) -> &'static str {
    match result {
        SolverCheckResult::Sat => "sat",
        SolverCheckResult::Unsat => "unsat",
        SolverCheckResult::Unknown => "unknown",
    }
}
