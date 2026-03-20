use std::{
    sync::mpsc::{self, RecvTimeoutError},
    thread,
    time::Duration,
};

#[cfg(feature = "training")]
use std::env;

use yardbird::{
    cost_functions::array::array_bmc_cost_factory,
    model_from_options,
    smtlib_problem::{SMTLIBProblem, SMTLIBSolver},
    strategies::{Abstract, ProofStrategy},
    training::{reset_training_database, TrainingSession},
    Driver, YardbirdOptions,
};

#[cfg(feature = "training")]
use sqlx::Row;

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
    let mut options = YardbirdOptions::from_filename("examples/array/array_copy.vmt".to_string());
    options.track_instantiations = true;
    let vmt_model = model_from_options(&options);
    let instantiation_strategy = options.build_instantiation_strategy();

    let result = run_with_timeout(
        move || {
            let mut driver = Driver::new(vmt_model, instantiation_strategy)
                .with_tracking_options(None, true, None);
            let strat: Box<dyn ProofStrategy<_>> =
                Box::new(Abstract::new(10, false, array_bmc_cost_factory));
            driver
                .check_strategy(options.depth, strat)
                .unwrap_or_default()
        },
        Duration::from_secs(20),
    );

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
    assert!(result.total_refinement_steps > 0);
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
            let strategy: Box<dyn ProofStrategy<_>> =
                Box::new(Abstract::new(0, false, array_bmc_cost_factory));
            SMTLIBSolver::execute_with_strategy(&problem, strategy, 50, true)
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

    let vmt_model = model_from_options(&options);
    let instantiation_strategy = options.build_instantiation_strategy();

    run_with_timeout(
        move || {
            let mut session = TrainingSession::from_options(&options)
                .expect("training session setup failed")
                .expect("training session should be enabled");
            let mut driver = Driver::new(vmt_model, instantiation_strategy)
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
    });
}
