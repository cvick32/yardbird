use std::time::Duration;

use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};
use yardbird::{
    policy::effort::EffortRecordKind, solver::SolverCheckResult, training::PolicyTrace, Driver,
    ProofLoopResult, SolverBackend, YardbirdOptions,
};

fn array_run(train: bool) -> ProofLoopResult {
    let mut options = YardbirdOptions::from_filename("examples/array/array_copy.vmt".into());
    options.depth = 3;
    options.train = train;
    options.record_decisions = true;
    Driver::new(
        yardbird::model_from_options(&options),
        options.build_instantiation_strategy(),
        SolverBackend::Z3,
    )
    .with_profiler(options.build_profiler())
    .check_strategy(options.depth, options.build_array_strategy())
    .unwrap()
}

fn binder_run(contradiction: bool) -> ProofLoopResult {
    let source = format!(
        "(declare-fun a () (Array Bool Bool))
         (declare-fun p (Bool) Bool)
         (define-fun init () Bool (! (and (forall ((x Bool)) (p x)) {}) :init true))
         (define-fun trans () Bool (! true :trans true))
         (define-fun prop () Bool (! false :invar-property 0))",
        if contradiction {
            "(not (p true))"
        } else {
            "(and (p true) (p false))"
        }
    );
    let commands = CommandStream::new(source.as_bytes(), SyntaxBuilder, None)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let model = VMTModel::checked_from(commands).unwrap();
    let mut options = YardbirdOptions::from_filename("policy-trace-binder.vmt".into());
    options.train = true;
    Driver::new(
        model,
        options.build_instantiation_strategy(),
        SolverBackend::Z3,
    )
    .with_profiler(options.build_profiler())
    .with_wall_timeout(Some(Duration::from_secs(2)))
    .check_strategy(1, options.build_array_strategy())
    .unwrap()
}

#[test]
fn training_enables_hooks_without_changing_instance_selection() {
    let plain = array_run(false);
    let observed = array_run(true);
    assert!(plain.profiling.solver_checks.is_empty());
    assert!(plain.profiling.cost_records.is_empty());
    assert_eq!(plain.used_instances, observed.used_instances);
    assert_eq!(
        plain.total_refinement_steps,
        observed.total_refinement_steps
    );
    let selected = |result: &ProofLoopResult| {
        result
            .abstract_instantiations
            .iter()
            .filter(|candidate| candidate.was_selected)
            .map(|candidate| candidate.abstract_instantiation_id.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(selected(&plain), selected(&observed));

    let trace = PolicyTrace::from_result(&observed);
    assert!(!trace.decisions.is_empty());
    assert!(!trace.installations.is_empty());
    assert!(trace
        .checks
        .iter()
        .any(|check| check.result == SolverCheckResult::Sat));
    assert!(trace
        .checks
        .iter()
        .any(|check| check.result == SolverCheckResult::Unsat));
    for attempt in &trace.installations {
        let id = attempt
            .installation
            .abstract_instantiation_id
            .as_ref()
            .unwrap();
        assert!(trace.decisions.iter().any(|decision| decision
            .candidates
            .iter()
            .any(|candidate| &candidate.abstract_instantiation_id == id && candidate.selected)));
        assert!(attempt.installation.result.is_some());
        let before = attempt.preceding_check_id.unwrap();
        let after = attempt.subsequent_check_id.unwrap();
        assert_eq!(after, before + 1);
    }
    let json = serde_json::to_value(&trace).unwrap();
    assert!(
        !json.to_string().contains("operation_id"),
        "transient offer handles must not become persistent identities"
    );
    let restored: PolicyTrace = serde_json::from_value(json).unwrap();
    assert_eq!(restored.decisions.len(), trace.decisions.len());
}

#[test]
fn binder_pages_link_to_enclosing_decisions_and_checks() {
    let result = binder_run(true);
    assert_eq!(
        result.run_progress.as_ref().unwrap().termination_reason,
        "depth_limit"
    );
    let trace = PolicyTrace::from_result(&result);
    let pages = trace
        .decisions
        .iter()
        .filter(|d| d.kind == EffortRecordKind::BinderPage)
        .collect::<Vec<_>>();
    assert!(!pages.is_empty());
    for page in pages {
        let parent_id = page
            .parent_decision_index
            .expect("page belongs to a phase operation");
        assert!(parent_id < page.decision_index);
        let parent = &trace.decisions[parent_id as usize];
        assert_eq!(parent.kind, EffortRecordKind::Operation);
        assert_eq!(parent.preceding_check_id, page.preceding_check_id);
        assert_eq!(parent.subsequent_check_id, page.subsequent_check_id);
        assert!(page.offered.contains(&page.chosen));
    }
    for decision in &trace.decisions {
        if decision.kind == EffortRecordKind::ReturnToDriver {
            assert!(decision.allowance.is_none());
            assert_eq!(decision.stop_reason, "policy_handoff");
        }
    }
}

#[test]
fn timeout_retains_empty_work_and_has_no_invented_subsequent_check() {
    let result = binder_run(false);
    let trace = PolicyTrace::from_result(&result);
    assert_eq!(
        trace.outcome.progress.as_ref().unwrap().termination_reason,
        "timeout"
    );
    assert!(!trace.outcome.found_proof && !trace.outcome.counterexample);
    assert!(trace
        .decisions
        .iter()
        .any(|d| d.report.selected == 0 && d.allowance.is_some()));
    let last = trace.decisions.last().unwrap();
    assert!(last.preceding_check_id.is_some());
    assert!(last.subsequent_check_id.is_none());
    assert!(trace
        .decisions
        .iter()
        .any(|d| d.graph_version_after > d.graph_version_before));
}

#[test]
fn failed_smtlib_run_retains_its_check_and_error() {
    use yardbird::{
        problem_context::ProblemContext,
        smtlib_problem::{
            RefinementFailure, RefinementLimits, SMTLIBProblem, SmtlibRefinementRunner,
        },
        strategies::{ProofAction, ProofStrategy},
        theory_support::{ConcreteArrayTheory, TheorySupport},
    };
    struct FailsAfterCheck;
    impl ProofStrategy<'_, ()> for FailsAfterCheck {
        fn get_theory_support(&self) -> Box<dyn TheorySupport> {
            Box::new(ConcreteArrayTheory::new(vec![("Int".into(), "Int".into())]))
        }
        fn setup(&mut self, _: &dyn ProblemContext, _: u16) -> yardbird::Result<()> {
            Ok(())
        }
        fn sat(
            &mut self,
            _: &mut (),
            _: &dyn ProblemContext,
            _: u32,
        ) -> yardbird::Result<ProofAction> {
            Err(anyhow::anyhow!("injected failure after check").into())
        }
        fn unsat(&mut self, _: &mut (), _: &dyn ProblemContext) -> yardbird::Result<ProofAction> {
            unreachable!()
        }
        fn result(&mut self, _: &mut VMTModel, _: &dyn ProblemContext) -> ProofLoopResult {
            unreachable!()
        }
    }
    let input = CommandStream::new(
        "(set-logic QF_AUFLIA) (declare-fun a () (Array Int Int)) (assert true) (check-sat)"
            .as_bytes(),
        SyntaxBuilder,
        None,
    )
    .collect::<Result<Vec<_>, _>>()
    .unwrap();
    let problem = SMTLIBProblem::from_commands(input).unwrap();
    let mut options = YardbirdOptions::from_filename("failed-trace.smt2".into());
    options.train = true;
    let error = SmtlibRefinementRunner::execute(
        &problem,
        Box::new(FailsAfterCheck),
        SolverBackend::Z3,
        RefinementLimits {
            max_refinements: Some(1),
            ..Default::default()
        },
        false,
        options.build_profiler(),
        None,
    )
    .unwrap_err();
    let failure = error
        .downcast_ref::<RefinementFailure>()
        .unwrap_or_else(|| panic!("expected a partial result, got {error:#}"));
    let trace = PolicyTrace::from_result(&failure.result);
    assert_eq!(trace.checks.len(), 1);
    assert_eq!(trace.checks[0].result, SolverCheckResult::Sat);
    let progress = trace.outcome.progress.unwrap();
    assert_eq!(progress.termination_reason, "error");
    assert!(progress.error.unwrap().contains("injected failure"));
}

#[cfg(feature = "training")]
#[test]
fn database_retains_linked_policy_trace_including_timeout() {
    use sqlx::Row;
    use yardbird::training::TrainingSession;
    let Ok(url) = std::env::var("YARDBIRD_TEST_DATABASE_URL") else {
        eprintln!("skipping database test: YARDBIRD_TEST_DATABASE_URL is unset");
        return;
    };
    let run_id = format!(
        "policy-trace-test-{}-{:?}",
        std::process::id(),
        std::time::SystemTime::now()
    );
    let results = [array_run(true), binder_run(false)];
    for (index, result) in results.iter().enumerate() {
        let mut options = YardbirdOptions::from_filename(format!("{run_id}-{index}"));
        options.train = true;
        options.database_url = Some(url.clone());
        options.training_run_version = Some(run_id.clone());
        TrainingSession::from_options(&options)
            .unwrap()
            .unwrap()
            .complete_result(result)
            .unwrap();
    }
    tokio::runtime::Runtime::new().unwrap().block_on(async {
        let pool = sqlx::PgPool::connect(&url).await.unwrap();
        for (index, result) in results.iter().enumerate() {
            let benchmark = sqlx::query("SELECT id, success, total_refinements FROM benchmarks WHERE name = $1")
                .bind(format!("{run_id}-{index}")).fetch_one(&pool).await.unwrap();
            let id: i64 = benchmark.get("id");
            assert_eq!(benchmark.get::<bool, _>("success"), index == 0);
            assert_eq!(benchmark.get::<i32, _>("total_refinements"), result.total_refinement_steps as i32);
            let trace = PolicyTrace::from_result(result);
            let count: i64 = sqlx::query_scalar("SELECT count(*) FROM effort_decisions WHERE benchmark_id = $1")
                .bind(id).fetch_one(&pool).await.unwrap();
            assert_eq!(count, trace.decisions.len() as i64);
            let record: sqlx::types::Json<serde_json::Value> = sqlx::query_scalar("SELECT record FROM policy_run_outcomes WHERE benchmark_id = $1")
                .bind(id).fetch_one(&pool).await.unwrap();
            assert_eq!(record.0["progress"]["termination_reason"], if index == 0 { "depth_limit" } else { "timeout" });
            if index == 0 {
                let linked: i64 = sqlx::query_scalar("SELECT count(*) FROM effort_candidates c JOIN abstract_instantiations a ON a.id = c.abstract_instantiation_db_id JOIN effort_decisions d ON d.benchmark_id = c.benchmark_id AND d.decision_index = c.decision_index WHERE c.benchmark_id = $1 AND c.selected AND d.subsequent_check_id IS NOT NULL")
                    .bind(id).fetch_one(&pool).await.unwrap();
                assert!(linked > 0);
                let installs: i64 = sqlx::query_scalar("SELECT count(*) FROM policy_installations WHERE benchmark_id = $1")
                    .bind(id).fetch_one(&pool).await.unwrap();
                assert_eq!(installs, trace.installations.len() as i64);
            }
        }
    });
}
