use super::*;
use crate::{
    instance_installation::assertion_tracker::canonical_instantiation_key,
    problem_context::ProblemContext,
    solver::SolverCheckResult,
    strategies::{ProofStrategy, RefinementState},
    vmt_bmc_session::VmtBmcSession,
};
use clap::Parser;
use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};
use std::{collections::HashSet, path::Path};

const INPUT: &str = r#"
    (declare-fun a () (Array Int Int))
    (declare-fun unused () (Array Int Int))
    (define-fun init () Bool (! (and
        (= (select (store a 1 7) 1) 9)
        (= (select unused 123) 42)) :init true))
    (define-fun trans () Bool (! true :trans true))
    (define-fun prop () Bool (! (= (select (store a 1 7) 1) 7) :invar-property 0))
"#;

fn model(source: &str) -> VMTModel {
    VMTModel::checked_from(
        CommandStream::new(source.as_bytes(), SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap(),
    )
    .unwrap()
}

fn fixture() -> VmtBmcSession {
    let mut strategy: Box<dyn ProofStrategy<'_, RefinementState>> =
        Box::new(Abstract::<ArrayBMCCost>::new(
            1,
            false,
            YardbirdPolicy::new(()),
            false,
        ));
    let model = strategy.configure_model(model(INPUT));
    let mut smt = VmtBmcSession::new(
        &model,
        &strategy,
        SolverBackend::Z3,
        false,
        Box::new(FullUnrollStrategy::new()),
        false,
        None,
    )
    .unwrap();
    assert_eq!(smt.check_property(), SolverCheckResult::Sat);
    smt
}

fn context<'a>(
    smt: &'a VmtBmcSession,
    pending: &'a HashSet<smt2parser::concrete::Term>,
) -> DiscoveryContext<'a> {
    DiscoveryContext {
        quantifiers: None,
        smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending,
    }
}

fn events(path: &Path) -> Vec<Value> {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|s| serde_json::from_str(s).unwrap())
        .collect()
}

#[test]
fn seeded_sampling_is_reproducible_well_sorted_and_covers_unfiltered_domains() {
    let smt = fixture();
    let pending = HashSet::new();
    let snapshot = InstantiationSession::default()
        .capture(&context(&smt, &pending), INPUT)
        .unwrap();
    let sampler = ProposalSampler::new(&snapshot);
    let mut left = StdRng::seed_from_u64(17);
    let mut right = StdRng::seed_from_u64(17);
    let mut other = StdRng::seed_from_u64(18);
    let mut different = false;
    let mut rules = BTreeMap::<String, usize>::new();
    let mut terms = HashSet::new();
    for _ in 0..3000 {
        let proposal = sampler.sample(&mut left).unwrap();
        let serialized = serde_json::to_value(&proposal).unwrap();
        assert_eq!(
            serialized,
            serde_json::to_value(sampler.sample(&mut right).unwrap()).unwrap()
        );
        different |=
            serialized != serde_json::to_value(sampler.sample(&mut other).unwrap()).unwrap();
        snapshot.resolve(&proposal).unwrap(); // Verifies every required slot and sort.
        *rules.entry(proposal.axiom_id).or_default() += 1;
        terms.extend(proposal.bindings.into_values());
    }
    assert!(different);
    assert_eq!(rules.len(), snapshot.schemas.len());
    assert!(rules.values().all(|n| (800..1200).contains(n)), "{rules:?}");
    // Even the unrelated source terms are available; no relevance or value pruning.
    assert!(snapshot.terms.iter().all(|term| terms.contains(&term.id)));
}

#[test]
fn missing_sort_domains_remove_only_ineligible_axioms() {
    let smt = fixture();
    let pending = HashSet::new();
    let mut snapshot = InstantiationSession::default()
        .capture(&context(&smt, &pending), INPUT)
        .unwrap();
    snapshot.terms.retain(|term| term.sort == "Int");
    let sampler = ProposalSampler::new(&snapshot);
    assert_eq!(sampler.schemas.len(), 1);
    assert!(sampler.schemas[0].name().starts_with("constant-array"));
    let mut rng = StdRng::seed_from_u64(0);
    snapshot
        .resolve(&sampler.sample(&mut rng).unwrap())
        .unwrap();
    snapshot.terms.clear();
    assert!(ProposalSampler::new(&snapshot).sample(&mut rng).is_none());
}

#[test]
fn discovery_accepts_only_shared_validation_and_counts_duplicate_samples_against_budget() {
    let dir = tempfile::tempdir().unwrap();
    let input = dir.path().join("input.vmt");
    std::fs::write(&input, INPUT).unwrap();
    let mut run = YardbirdOptions {
        policy: Some(NamedPolicy::RandomInstantiation),
        filename: Some(input.to_string_lossy().into_owned()),
        no_guided_fallback: true,
        random: RandomOptions {
            random_seed: 0,
            random_samples: 1000,
            random_log: Some(dir.path().join("accepted.jsonl")),
        },
        ..Default::default()
    };
    let smt = fixture();
    let mut pending = HashSet::new();
    let accepted = RandomDiscovery::new(&run)
        .discover(&context(&smt, &pending))
        .unwrap();
    assert_eq!(accepted.len(), 1);
    let instance = &accepted[0];
    assert_eq!(
        smt.eval_partial(&instance.term).unwrap(),
        crate::solver::api::ModelEvaluation::Known("false".into())
    );
    let records = events(run.random.random_log.as_ref().unwrap());
    let attempts = records
        .iter()
        .filter(|e| e["event"] == "attempt_result")
        .count();
    assert!((1..=1000).contains(&attempts));
    assert_eq!(records.last().unwrap()["samples"], attempts);
    assert_eq!(records.last().unwrap()["outcome"], "violated");
    assert!(records
        .iter()
        .all(|e| e["event"] != "request" && e.get("cost").is_none()));

    let normalized = smt
        .make_unquantified_instance(instance.term.clone())
        .unwrap();
    pending.insert(canonical_instantiation_key(normalized.get_term()));
    run.random.random_samples = attempts;
    run.random.random_log = Some(dir.path().join("duplicate.jsonl"));
    assert!(RandomDiscovery::new(&run)
        .discover(&context(&smt, &pending))
        .unwrap()
        .is_empty());
    let records = events(run.random.random_log.as_ref().unwrap());
    assert_eq!(records.last().unwrap()["outcome"], "budget_exhausted");
    assert_eq!(records.last().unwrap()["samples"], attempts);
    assert_eq!(
        records[records.len() - 2]["feedback"]["outcome"],
        "already_present"
    );
    assert_eq!(records.last().unwrap()["ordinary_fallback"], false);
    assert!(smt.get_instantiations().is_empty()); // Discovery never installs directly.
}

#[test]
fn strict_exhaustion_is_inconclusive_even_on_a_real_counterexample() {
    let dir = tempfile::tempdir().unwrap();
    let input = dir.path().join("counterexample.vmt");
    let source = r#"
        (declare-fun a () (Array Int Int))
        (define-fun init () Bool (! (= (select a 0) 0) :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! false :invar-property 0))
    "#;
    std::fs::write(&input, source).unwrap();
    let run = YardbirdOptions {
        policy: Some(NamedPolicy::RandomInstantiation),
        depth: 1,
        filename: Some(input.to_string_lossy().into_owned()),
        no_guided_fallback: true,
        random: RandomOptions {
            random_samples: 3,
            random_log: Some(dir.path().join("random.jsonl")),
            ..Default::default()
        },
        ..Default::default()
    };
    run.random.validate(&run).unwrap();
    let plan = build_plan(&run);
    let mut driver = crate::Driver::new(model(source), plan.instantiation_strategy, plan.solver);
    let error = driver.check_strategy(1, plan.strategy).unwrap_err();
    assert!(matches!(error, crate::driver::Error::NoProgress { .. }));
    let failed = driver.take_failed_result().unwrap();
    assert!(!failed.counterexample && !failed.found_proof);
    assert_eq!(failed.total_instantiations_added, 0);
    let records = events(run.random.random_log.as_ref().unwrap());
    assert_eq!(records.last().unwrap()["samples"], 3);
}

#[test]
fn random_options_roundtrip_validate_without_credentials_and_preserve_old_json() {
    let dir = tempfile::tempdir().unwrap();
    let log = dir.path().join("new.jsonl");
    let run = YardbirdOptions::try_parse_from([
        "yardbird",
        "-f",
        "fixture.vmt",
        "--policy",
        "random-instantiation",
        "--random-seed",
        "42",
        "--random-samples",
        "1000",
        "--no-guided-fallback",
        "--random-log",
        log.to_str().unwrap(),
    ])
    .unwrap();
    run.random.validate(&run).unwrap();
    run.llm.validate(&run).unwrap();
    run.decision_model.validate(&run).unwrap();
    run.validate_guided_fallback().unwrap();
    let decoded: YardbirdOptions =
        serde_json::from_value(serde_json::to_value(&run).unwrap()).unwrap();
    assert_eq!(decoded.random, run.random);
    let mut old = serde_json::to_value(YardbirdOptions::default()).unwrap();
    old.as_object_mut().unwrap().remove("random");
    assert_eq!(
        serde_json::from_value::<YardbirdOptions>(old)
            .unwrap()
            .random,
        RandomOptions::default()
    );
    let mut invalid = run.clone();
    invalid.random.random_samples = 0;
    assert!(invalid.random.validate(&invalid).is_err());
    invalid = run.clone();
    invalid.policy = None;
    assert!(invalid.random.validate(&invalid).is_err());
    invalid = run.clone();
    invalid.filename = Some("fixture.smt2".into());
    assert!(invalid.random.validate(&invalid).is_err());
    invalid = run.clone();
    invalid.random.random_log = None;
    assert!(invalid.random.validate(&invalid).is_err());
    std::fs::write(log, "old evidence").unwrap();
    assert!(run.random.validate(&run).is_err());
}
