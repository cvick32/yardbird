use yardbird::{
    auxiliary_synthesis::AuxSynthesisConfig,
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
        (),
        AuxSynthesisConfig::default(),
        false,
    ));

    let result = SmtlibRefinementRunner::execute(
        &problem,
        strategy,
        SolverBackend::Z3,
        5,
        false,
        options.build_profiler(),
        None,
    )
    .unwrap()
    .0;

    assert!(!result.profiling.solver_checks.is_empty());
}
