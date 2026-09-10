use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};
use yardbird::{
    cost_functions::array::ArrayBMCCost, instantiation_strategy::full_unroll::FullUnrollStrategy,
    solver::PropertyCheckMode, strategies::Abstract, Driver, SolverBackend,
};

fn model() -> VMTModel {
    let input = r#"
        (declare-fun a () (Array Int Int))
        (declare-fun a_next () (Array Int Int))
        (define-fun .a () (Array Int Int) (! a :next a_next))
        (declare-fun b () (Array Int Int))
        (declare-fun b_next () (Array Int Int))
        (define-fun .b () (Array Int Int) (! b :next b_next))
        (define-fun init () Bool (! (and
            (= a ((as const (Array Int Int)) 0))
            (= b ((as const (Array Int Int)) 0))) :init true))
        (define-fun transition () Bool (! (and
            (=> true (= a_next (store a 0 1)))
            (=> true (= b_next (store b 0 2)))) :trans true))
        (define-fun property () Bool (! (and
            (= (select a 1) 0) (= (select b 1) 0)) :invar-property 0))
    "#;
    let commands = CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    VMTModel::checked_from(commands).unwrap()
}

fn run(enabled: bool, budget: usize) -> yardbird::ProofLoopResult {
    let mut driver = Driver::new(
        model(),
        Box::new(FullUnrollStrategy::new()),
        SolverBackend::Z3,
    );
    let strategy = Abstract::<ArrayBMCCost>::new(4, false, (), false)
        .with_guarded_read_updates(enabled)
        .with_candidate_winners_per_group(budget)
        .with_property_check_mode(PropertyCheckMode::Assumptions);
    driver.check_strategy(4, Box::new(strategy)).unwrap()
}

#[test]
fn guarded_schemas_are_lazy_and_use_the_configured_budget() {
    let narrow = run(true, 1);
    let wide = run(true, 16);
    for result in [&narrow, &wide] {
        assert!(!result.counterexample);
        assert!(
            result
                .solver_statistics
                .get_f64("yardbird encoding guarded schemas installed")
                .unwrap()
                > 0.0
        );
        assert_eq!(
            result
                .solver_statistics
                .get_f64("yardbird encoding guarded eager schemas"),
            Some(0.0)
        );
    }
    assert_eq!(
        narrow
            .solver_statistics
            .get_f64("yardbird encoding guarded max batch"),
        Some(1.0)
    );
    let wide_max = wide
        .solver_statistics
        .get_f64("yardbird encoding guarded max batch")
        .unwrap();
    assert!(wide_max > 1.0 && wide_max <= 16.0);
}

#[test]
fn disabled_transform_keeps_the_baseline_path() {
    let result = run(false, 16);
    assert!(!result.counterexample);
    assert_eq!(
        result
            .solver_statistics
            .get_f64("yardbird encoding guarded schemas planned"),
        None
    );
}

#[test]
fn cli_rejects_unsupported_guarded_updates_before_loading_input() {
    for args in [
        vec!["--filename", "missing.vmt", "--strategy", "concrete"],
        vec![
            "--filename",
            "missing.vmt",
            "--strategy",
            "abstract-with-quantifiers",
        ],
        vec!["--filename", "missing.vmt", "--theory", "list"],
        vec!["--filename", "missing.vmt", "--theory", "bv-list"],
        vec!["--filename", "missing.smt2"],
    ] {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_yardbird"))
            .args(&args)
            .arg("--guarded-read-updates")
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success(), "{args:?}");
        assert!(
            stderr.contains("--guarded-read-updates requires VMT input, --theory array, and --strategy abstract"),
            "{args:?}: {stderr}"
        );
    }
}

#[test]
fn cli_accepts_guarded_abstract_and_unguarded_concrete_runs() {
    for args in [
        vec!["--strategy", "abstract", "--guarded-read-updates"],
        vec!["--strategy", "concrete"],
    ] {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_yardbird"))
            .args([
                "--filename",
                "examples/array/array_copy.vmt",
                "--depth",
                "1",
            ])
            .args(&args)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
