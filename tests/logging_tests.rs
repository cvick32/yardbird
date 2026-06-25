use std::{
    sync::mpsc::{self, RecvTimeoutError},
    thread,
    time::Duration,
};

#[cfg(feature = "training")]
use std::env;

use yardbird::{
    auxiliary_synthesis::AuxSynthesisConfig,
    cost_functions::array::array_bmc_cost_factory,
    model_from_options,
    smtlib_problem::{SMTLIBProblem, SMTLIBSolver},
    strategies::{Abstract, ProofStrategy},
    training::{
        reset_training_database, AbstractInstantiationRecord, CandidateRecord, DecisionRecord,
        IndexedInstantiationRecord, TrainingSession, UnsatEventRecord,
    },
    Driver, SolverBackend, YardbirdOptions,
};

#[cfg(feature = "training")]
use sqlx::Row;

fn json_number(value: &serde_json::Value, key: &str) -> f64 {
    value
        .get(key)
        .and_then(serde_json::Value::as_f64)
        .unwrap_or_else(|| panic!("expected numeric JSON value for key `{key}`"))
}

fn run_array_copy_logging_result() -> yardbird::ProofLoopResult {
    let mut options = YardbirdOptions::from_filename("examples/array/array_copy.vmt".to_string());
    options.track_instantiations = true;
    let vmt_model = model_from_options(&options);
    let instantiation_strategy = options.build_instantiation_strategy();

    run_with_timeout(
        move || {
            let mut driver = Driver::new(vmt_model, instantiation_strategy, SolverBackend::Z3)
                .with_tracking_options(None, true, None);
            let strat: Box<dyn ProofStrategy<_>> = Box::new(Abstract::new(
                10,
                false,
                array_bmc_cost_factory,
                AuxSynthesisConfig::default(),
            ));
            driver
                .check_strategy(options.depth, strat)
                .unwrap_or_default()
        },
        Duration::from_secs(20),
    )
}

fn run_with_timeout<F, T>(f: F, timeout: Duration) -> T
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + Default + 'static,
{
    let (tx, rx) = mpsc::channel();
    let _ = thread::spawn(move || {
        let result = f();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => result,
        Err(RecvTimeoutError::Timeout) => panic!("benchmark run timed out after {:?}", timeout),
        Err(RecvTimeoutError::Disconnected) => {
            panic!("benchmark thread disconnected before returning")
        }
    }
}

#[test]
fn array_strategy_populates_decision_data() {
    let result = run_array_copy_logging_result();

    assert!(
        !result.decision_data.is_empty(),
        "expected at least one logged decision"
    );
    assert!(
        result.decision_data.iter().all(|decision| decision
            .candidates
            .iter()
            .any(|candidate| candidate.was_chosen)),
        "every decision should record a chosen candidate"
    );
    assert!(
        !result.indexed_instantiations.is_empty(),
        "tracked instantiations should be exported when tracking is enabled"
    );
    assert!(
        !result.abstract_instantiations.is_empty(),
        "expected abstract instantiations to be logged"
    );
    assert!(
        result
            .abstract_instantiations
            .iter()
            .any(|inst| !inst.decision_keys.is_empty()),
        "expected at least one abstract instantiation to point back to decisions"
    );
    assert!(
        result
            .indexed_instantiations
            .iter()
            .any(|inst| inst.abstract_instantiation_id.is_some()),
        "expected indexed instantiations to carry abstract instantiation ids"
    );
    assert!(
        result
            .abstract_instantiations
            .iter()
            .all(|inst| !inst.term.contains('@')),
        "abstract instantiation terms should be deindexed before logging"
    );
    assert!(
        result
            .indexed_instantiations
            .iter()
            .any(|inst| inst.term.contains('@')),
        "indexed instantiation terms should preserve frame indices"
    );
    assert!(result.total_refinement_steps > 0);
}

#[test]
fn proof_loop_result_json_roundtrip_preserves_logging_artifacts() {
    let mut chosen_candidate = CandidateRecord::new("i@0".to_string(), "term-hash".to_string());
    chosen_candidate.was_chosen = true;

    let result = yardbird::ProofLoopResult {
        decision_data: vec![DecisionRecord {
            decision_key: "decision-key".to_string(),
            bmc_depth: 3,
            axiom_name: "read-after-write".to_string(),
            slot_index: 1,
            candidates: vec![chosen_candidate],
        }],
        abstract_instantiations: vec![AbstractInstantiationRecord {
            abstract_instantiation_id: "abstract-inst".to_string(),
            term: "(= x y)".to_string(),
            term_hash: "abstract-hash".to_string(),
            axiom_name: "read-after-write".to_string(),
            bmc_depth: 3,
            refinement_step: 4,
            decision_keys: vec!["decision-key".to_string()],
            in_unsat_core: true,
        }],
        indexed_instantiations: vec![IndexedInstantiationRecord {
            label: "inst_0_3".to_string(),
            term: "(= x@0 y@0)".to_string(),
            term_hash: "indexed-hash".to_string(),
            depth: 3,
            unroll_index: 0,
            abstract_instantiation_id: Some("abstract-inst".to_string()),
            in_unsat_core: true,
        }],
        unsat_events: vec![UnsatEventRecord {
            event_index: 0,
            bmc_depth: Some(3),
            global_refinement_step: Some(4),
            check_sat_index: None,
            total_instantiations_added: 7,
            instantiations_since_last_unsat: 2,
            core_size: Some(1),
            conflicts: Some(5.0),
            decisions: Some(8.0),
            restarts: None,
            propagations: Some(13.0),
            array_ax1: None,
            array_ax2: None,
            array_ext_ax: None,
            solver_stats_snapshot: serde_json::json!({ "conflicts": 5.0 }),
            solver_stats_delta: serde_json::json!({ "conflicts": 2.0 }),
        }],
        ..Default::default()
    };

    let encoded = serde_json::to_string(&result).expect("should serialize proof result");
    let decoded: yardbird::ProofLoopResult =
        serde_json::from_str(&encoded).expect("should deserialize proof result");

    assert_eq!(decoded.decision_data.len(), 1);
    assert_eq!(decoded.abstract_instantiations.len(), 1);
    assert_eq!(decoded.indexed_instantiations.len(), 1);
    assert_eq!(decoded.unsat_events.len(), 1);
    assert_eq!(
        decoded.abstract_instantiations[0].decision_keys,
        vec!["decision-key"]
    );
    assert_eq!(decoded.unsat_events[0].total_instantiations_added, 7);
}

#[test]
fn array_copy_logs_expected_unsat_event_shape() {
    let result = run_array_copy_logging_result();

    assert_eq!(
        result.unsat_events.len(),
        10,
        "array_copy at depth 10 should produce one unsat event per depth"
    );
    assert_eq!(
        result
            .unsat_events
            .last()
            .map(|event| event.total_instantiations_added),
        Some(result.total_instantiations_added)
    );
    assert_eq!(
        result
            .unsat_events
            .last()
            .and_then(|event| event.global_refinement_step),
        Some(result.total_refinement_steps)
    );
    assert_eq!(
        result.unsat_events.last().and_then(|event| event.core_size),
        result.unsat_core.as_ref().map(|core| core.core_size as u32)
    );

    let expected_instantiation_deltas = [0_u64, 0, 3, 5, 2, 2, 2, 2, 2, 2];
    for (index, event) in result.unsat_events.iter().enumerate() {
        assert_eq!(event.event_index as usize, index);
        assert_eq!(event.bmc_depth, Some(index as u16));
        assert_eq!(event.check_sat_index, None);
        assert_eq!(
            event.instantiations_since_last_unsat, expected_instantiation_deltas[index],
            "unexpected instantiation delta at unsat event {index}"
        );
        if index > 0 {
            assert!(
                event.total_instantiations_added
                    >= result.unsat_events[index - 1].total_instantiations_added
            );
            assert!(
                event.core_size.unwrap_or_default()
                    >= result.unsat_events[index - 1].core_size.unwrap_or_default()
            );
        }
    }
}

#[test]
fn unsat_event_stats_snapshots_and_deltas_are_consistent() {
    let result = run_array_copy_logging_result();
    let first_event = &result.unsat_events[0];
    let previous_event = &result.unsat_events[2];
    let later_event = &result.unsat_events[3];

    assert_eq!(
        json_number(&first_event.solver_stats_snapshot, "conflicts"),
        json_number(&first_event.solver_stats_delta, "conflicts"),
        "the first unsat event should use its snapshot as the delta baseline"
    );
    assert_eq!(first_event.conflicts, Some(1.0));

    let later_conflicts = json_number(&later_event.solver_stats_snapshot, "conflicts");
    let previous_conflicts = json_number(&previous_event.solver_stats_snapshot, "conflicts");
    let conflict_delta = json_number(&later_event.solver_stats_delta, "conflicts");
    assert_eq!(later_event.conflicts, Some(later_conflicts));
    assert!(
        (conflict_delta - (later_conflicts - previous_conflicts)).abs() < 1e-9,
        "expected delta conflicts to match snapshot difference"
    );

    let later_decisions = json_number(&later_event.solver_stats_snapshot, "decisions");
    let decision_delta = json_number(&later_event.solver_stats_delta, "decisions");
    let previous_decisions = previous_event
        .solver_stats_snapshot
        .get("decisions")
        .and_then(serde_json::Value::as_f64)
        .unwrap_or(0.0);
    assert_eq!(later_event.decisions, Some(later_decisions));
    assert!(
        (decision_delta - (later_decisions - previous_decisions)).abs() < 1e-9,
        "expected delta decisions to match snapshot difference"
    );
}

#[test]
fn training_session_requires_build_or_configuration() {
    let mut options = YardbirdOptions::from_filename("examples/array/array_copy.vmt".to_string());
    options.train = true;

    #[cfg(not(feature = "training"))]
    {
        let err = TrainingSession::from_options(&options).unwrap_err();
        assert!(
            err.to_string()
                .contains("built without the `training` feature"),
            "unexpected error: {err}"
        );
    }

    #[cfg(feature = "training")]
    {
        let err = TrainingSession::from_options(&options).unwrap_err();
        assert!(
            err.to_string()
                .contains("--train requires --database-url or YARDBIRD_DATABASE_URL"),
            "unexpected error: {err}"
        );
    }
}

#[test]
fn training_reset_requires_build_or_configuration() {
    #[cfg(not(feature = "training"))]
    {
        let err = reset_training_database(None).unwrap_err();
        assert!(
            err.to_string()
                .contains("built without the `training` feature"),
            "unexpected error: {err}"
        );
    }

    #[cfg(feature = "training")]
    {
        let err = reset_training_database(None).unwrap_err();
        assert!(
            err.to_string()
                .contains("--train-reset requires --database-url or YARDBIRD_DATABASE_URL"),
            "unexpected error: {err}"
        );
    }
}

#[test]
fn filename_is_only_optional_for_reset_mode() {
    let options = YardbirdOptions::default();
    let err = options.require_filename().unwrap_err();
    assert!(
        err.to_string()
            .contains("--filename is required unless --train-reset is used"),
        "unexpected error: {err}"
    );

    let reset_options = YardbirdOptions {
        train_reset: true,
        ..Default::default()
    };
    assert!(reset_options.filename.is_none());
}

#[test]
fn smtlib_strategy_populates_logging_artifacts() {
    let result = run_with_timeout(
        move || {
            let problem = SMTLIBProblem::from_path("examples/smt2/array_bitvec_simple.smt2")
                .expect("should parse SMT-LIB example");
            let strategy: Box<dyn ProofStrategy<_>> = Box::new(Abstract::new(
                0,
                false,
                array_bmc_cost_factory,
                AuxSynthesisConfig::default(),
            ));
            SMTLIBSolver::execute_with_strategy(&problem, strategy, SolverBackend::Z3, 50, true)
                .expect("SMT-LIB strategy run should complete")
                .0
        },
        Duration::from_secs(20),
    );

    assert!(
        !result.decision_data.is_empty(),
        "expected SMT-LIB strategy mode to log decisions"
    );
    assert!(
        !result.abstract_instantiations.is_empty(),
        "expected SMT-LIB strategy mode to log abstract instantiations"
    );
    assert!(
        !result.indexed_instantiations.is_empty(),
        "expected SMT-LIB strategy mode to export indexed instantiations"
    );
    assert!(
        result
            .abstract_instantiations
            .iter()
            .any(|inst| !inst.decision_keys.is_empty()),
        "expected at least one SMT-LIB abstract instantiation to point back to decisions"
    );
    assert!(
        result
            .indexed_instantiations
            .iter()
            .any(|inst| inst.abstract_instantiation_id.is_some()),
        "expected SMT-LIB indexed instantiations to carry abstract instantiation ids"
    );
    assert_eq!(result.unsat_events.len(), 1);
    let event = &result.unsat_events[0];
    assert_eq!(event.event_index, 0);
    assert_eq!(event.bmc_depth, None);
    assert_eq!(event.global_refinement_step, None);
    assert_eq!(event.check_sat_index, Some(1));
    assert_eq!(event.total_instantiations_added, 1);
    assert_eq!(event.instantiations_since_last_unsat, 1);
    assert_eq!(event.core_size, Some(1));
    assert_eq!(event.conflicts, Some(1.0));
    assert_eq!(event.decisions, Some(68.0));
    assert_eq!(event.propagations, Some(33.0));
}

#[cfg(feature = "training")]
#[test]
fn single_example_persists_provenance_to_db() {
    let database_url = match env::var("YARDBIRD_TEST_DATABASE_URL") {
        Ok(url) => url,
        Err(_) => {
            eprintln!("skipping DB integration test because YARDBIRD_TEST_DATABASE_URL is unset");
            return;
        }
    };

    let mut options = YardbirdOptions::from_filename("examples/array/array_copy.vmt".to_string());
    options.track_instantiations = true;
    options.train = true;
    options.database_url = Some(database_url.clone());
    options.training_run_version = Some("logging-test-run".to_string());

    let vmt_model = model_from_options(&options);
    let instantiation_strategy = options.build_instantiation_strategy();

    run_with_timeout(
        move || {
            let mut session = TrainingSession::from_options(&options)
                .expect("training session setup failed")
                .expect("training session should be enabled");
            let mut driver = Driver::new(vmt_model, instantiation_strategy, SolverBackend::Z3)
                .with_tracking_options(None, true, None);
            let strat: Box<dyn ProofStrategy<_>> =
                Box::new(Abstract::new(10, false, array_bmc_cost_factory));
            let result = driver
                .check_strategy(options.depth, strat)
                .expect("benchmark should complete");
            session
                .complete_result(&result)
                .expect("training session should persist result");
        },
        Duration::from_secs(20),
    );

    let runtime = tokio::runtime::Runtime::new().expect("failed to create runtime for DB test");
    runtime.block_on(async move {
        let pool = sqlx::postgres::PgPoolOptions::new()
            .max_connections(1)
            .connect(&database_url)
            .await
            .expect("failed to connect to test database");

        let benchmark_id: i64 =
            sqlx::query("SELECT id FROM benchmarks WHERE name = $1 ORDER BY id DESC LIMIT 1")
                .bind("examples/array/array_copy.vmt")
                .fetch_one(&pool)
                .await
                .expect("expected benchmark row")
                .get("id");
        let training_run = sqlx::query(
            r#"
            SELECT tr.run_version, tr.schema_version
            FROM benchmarks b
            JOIN training_runs tr ON tr.id = b.training_run_id
            WHERE b.id = $1
            "#,
        )
        .bind(benchmark_id)
        .fetch_one(&pool)
        .await
        .expect("expected linked training run row");

        let decision_count: i64 =
            sqlx::query("SELECT COUNT(*) AS count FROM decisions WHERE benchmark_id = $1")
                .bind(benchmark_id)
                .fetch_one(&pool)
                .await
                .expect("expected decision count")
                .get("count");
        let abstract_count: i64 = sqlx::query(
            "SELECT COUNT(*) AS count FROM abstract_instantiations WHERE benchmark_id = $1",
        )
        .bind(benchmark_id)
        .fetch_one(&pool)
        .await
        .expect("expected abstract instantiation count")
        .get("count");
        let indexed_count: i64 = sqlx::query(
            "SELECT COUNT(*) AS count FROM indexed_instantiations WHERE benchmark_id = $1",
        )
        .bind(benchmark_id)
        .fetch_one(&pool)
        .await
        .expect("expected indexed instantiation count")
        .get("count");
        let link_count: i64 = sqlx::query(
            r#"
            SELECT COUNT(*) AS count
            FROM abstract_instantiation_decisions aid
            JOIN abstract_instantiations ai ON ai.id = aid.abstract_instantiation_id
            WHERE ai.benchmark_id = $1
            "#,
        )
        .bind(benchmark_id)
        .fetch_one(&pool)
        .await
        .expect("expected abstract instantiation decision link count")
        .get("count");
        let unsat_event_count: i64 =
            sqlx::query("SELECT COUNT(*) AS count FROM unsat_events WHERE benchmark_id = $1")
                .bind(benchmark_id)
                .fetch_one(&pool)
                .await
                .expect("expected unsat event count")
                .get("count");
        let final_unsat_event = sqlx::query(
            r#"
            SELECT total_instantiations_added, core_size
            FROM unsat_events
            WHERE benchmark_id = $1
            ORDER BY event_index DESC
            LIMIT 1
            "#,
        )
        .bind(benchmark_id)
        .fetch_one(&pool)
        .await
        .expect("expected final unsat event row");

        assert!(decision_count > 0, "expected persisted decisions");
        assert!(
            abstract_count > 0,
            "expected persisted abstract instantiations"
        );
        assert!(
            indexed_count > 0,
            "expected persisted indexed instantiations"
        );
        assert!(link_count > 0, "expected persisted provenance links");
        assert_eq!(unsat_event_count, 10, "expected persisted unsat event rows");
        assert_eq!(
            training_run.get::<String, _>("run_version"),
            "logging-test-run"
        );
        assert_eq!(
            training_run.get::<String, _>("schema_version"),
            "004_training_runs"
        );
        assert_eq!(
            final_unsat_event.get::<i64, _>("total_instantiations_added"),
            20
        );
        assert_eq!(final_unsat_event.get::<i32, _>("core_size"), 15);
    });
}
