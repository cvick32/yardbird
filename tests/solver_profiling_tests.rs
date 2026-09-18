use yardbird::{
    cost_functions::array::ArrayBMCCost,
    model_from_options,
    smtlib_problem::{SMTLIBProblem, SmtlibCommandExecutor, SmtlibRefinementRunner},
    strategies::{Abstract, ProofStrategy},
    Driver, SolverBackend, Strategy, YardbirdOptions,
};

fn run_profiled_strategy(strategy: Strategy) -> yardbird::ProofLoopResult {
    let mut options = YardbirdOptions::from_filename("examples/array/array_copy.vmt".to_string());
    options.depth = 1;
    options.strategy = strategy;
    options.profile = true;

    let model = model_from_options(&options);
    let instantiation_strategy = options.build_instantiation_strategy();
    let mut driver = Driver::new(model, instantiation_strategy, SolverBackend::Z3)
        .with_profiler(options.build_profiler());

    driver
        .check_strategy(options.depth, options.build_array_strategy())
        .expect("depth-zero array_copy check should be UNSAT")
}

fn assert_complete_solver_profile(result: &yardbird::ProofLoopResult, strategy: &str) {
    let profiling = &result.profiling;
    assert!(!profiling.solver_checks.is_empty());
    assert!(!profiling.driver_records.is_empty());

    let run_id = &profiling.solver_checks[0].run_id;
    for (expected_check_id, check) in profiling.solver_checks.iter().enumerate() {
        assert_eq!(&check.run_id, run_id);
        assert_eq!(check.check_id, expected_check_id as u64);
        assert_eq!(check.benchmark_id, "examples/array/array_copy.vmt");
        assert_eq!(check.strategy, strategy);
        assert_eq!(check.depth, 0);
        assert_eq!(check.refinement_id, expected_check_id as u32 + 1);
        assert_eq!(check.refinement_step, expected_check_id as u32);
        assert_eq!(check.backend, SolverBackend::Z3);
        assert!(check.timing_ns.raw_check > 0);
        assert!(check.timing_ns.total_check_handling >= check.timing_ns.raw_check);
        assert!(check.statistics_before.to_json_value().is_object());
        assert!(check.statistics_after.to_json_value().is_object());
        assert!(check.statistics_delta.to_json_value().is_object());
    }
}

#[test]
fn concrete_strategy_emits_solver_profiles() {
    let result = run_profiled_strategy(Strategy::Concrete);
    assert_complete_solver_profile(&result, "concrete");
}

#[test]
fn concrete_timeout_retains_the_last_unsat_event_and_completion_log() {
    // This protocol's native checks grow expensive with depth, reproducing a
    // cooperative deadline crossed inside check_property rather than setup.
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "examples/distributed_protocols/client_server_ae/client_server_ae.encoding.vmt",
            "-s",
            "concrete",
            "-d",
            "40",
            "--property-check-mode",
            "assumptions",
            "--wall-timeout-secs",
            "1",
            "--profile",
            "--json-output",
        ])
        .env("RUST_LOG", "off,yardbird::driver=info")
        .env("RUST_LOG_STYLE", "never")
        .output()
        .unwrap();
    assert!(output.status.success());
    let result: yardbird::ProofLoopResult = serde_json::from_slice(&output.stdout).unwrap();
    let progress = result.run_progress.as_ref().unwrap();
    assert_eq!(progress.termination_reason, "timeout");
    assert_eq!(progress.last_completed_action.as_deref(), Some("check"));
    let checks = &result.profiling.solver_checks;
    assert!(!checks.is_empty());
    assert_eq!(result.unsat_events.len(), checks.len());
    assert_eq!(
        progress.deepest_completed_depth,
        result.unsat_events.last().and_then(|event| event.bmc_depth)
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    for check in checks {
        assert_eq!(check.result, yardbird::solver::SolverCheckResult::Unsat);
        assert!(stderr.contains(&format!(
            "BMC_DEPTH_COMPLETED depth={} elapsed_secs=",
            check.depth
        )));
    }
}

#[test]
fn abstract_strategy_emits_solver_profiles() {
    let result = run_profiled_strategy(Strategy::Abstract);
    assert_complete_solver_profile(&result, "abstract");
}

#[test]
fn simple_incremental_smtlib_profiles_every_check() {
    let mut options =
        YardbirdOptions::from_filename("examples/smtlib/incremental.smt2".to_string());
    options.profile = true;
    options.strategy = Strategy::Concrete;
    let problem = SMTLIBProblem::from_path(options.require_filename().unwrap()).unwrap();
    let mut solver =
        SmtlibCommandExecutor::new_with_backend(problem.get_logic(), SolverBackend::Z3, None)
            .unwrap()
            .with_profiler(options.build_profiler());

    solver.execute(&problem).unwrap();
    let profiling = solver.profiling();

    assert_eq!(profiling.solver_checks.len(), 5);
    for (check_id, record) in profiling.solver_checks.iter().enumerate() {
        assert_eq!(record.check_id, check_id as u64);
        assert_eq!(record.refinement_id, check_id as u32 + 1);
        assert_eq!(record.refinement_step, check_id as u32);
        assert!(record.timing_ns.raw_check > 0);
        assert!(record.statistics_after.get_f64("solver_time").is_some());
        assert!(record.statistics_delta.get_f64("solver_time").is_some());
    }
}

#[test]
fn strategy_smtlib_profiles_checks() {
    let mut options =
        YardbirdOptions::from_filename("examples/smt2/array_bitvec_simple.smt2".to_string());
    options.profile = true;
    let problem = SMTLIBProblem::from_path(options.require_filename().unwrap()).unwrap();
    let strategy: Box<dyn ProofStrategy<_>> = Box::new(Abstract::<ArrayBMCCost>::new(
        0,
        false,
        yardbird::YardbirdPolicy::new(()),
        false,
    ));

    let result = SmtlibRefinementRunner::execute(
        &problem,
        strategy,
        SolverBackend::Z3,
        yardbird::smtlib_problem::RefinementLimits {
            max_refinements: Some(5),
            ..Default::default()
        },
        false,
        options.build_profiler(),
        None,
    )
    .unwrap()
    .0;

    assert!(!result.profiling.solver_checks.is_empty());
}
