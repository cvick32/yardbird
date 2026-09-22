//! Exercise the actual CLI dispatch, including concrete SMT-LIB's eager path.
use std::{
    fs,
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};

use serde_json::Value;

const DECLARATIONS: &str = "
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
";
const PROPERTY: &str = "(= (select (store a i v) j) (ite (= i j) v (select a j)))";

fn run(extension: &str, options: &[&str]) -> Value {
    run_fixture(extension, options, PROPERTY, "1")
}

fn run_fixture(extension: &str, options: &[&str], property: &str, depth: &str) -> Value {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join(format!("eager.{extension}"));
    let body = if extension == "vmt" {
        format!(
            "{DECLARATIONS}
(define-fun a.link () (Array Int Int) (! a :next a.next))
(define-fun i.link () Int (! i :next i.next))
(define-fun j.link () Int (! j :next j.next))
(define-fun v.link () Int (! v :next v.next))
(define-fun init () Bool (! true :init true))
(define-fun trans () Bool (! true :trans true))
(define-fun prop () Bool (! {property} :invar-property 0))"
        )
    } else {
        format!("(set-logic QF_AUFLIA)\n{DECLARATIONS}\n(assert (not {property}))\n(check-sat)")
    };
    fs::write(&input, body).unwrap();
    let stdout = temp.path().join("stdout.json");
    let stderr = temp.path().join("stderr.log");
    eprintln!("CLI case: {extension} {options:?}");
    let mut child = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args(["-f", input.to_str().unwrap(), "-d", depth, "--json-output"])
        .args(options)
        .env("RUST_LOG", "off")
        .stdout(Stdio::from(fs::File::create(&stdout).unwrap()))
        .stderr(Stdio::from(fs::File::create(&stderr).unwrap()))
        .spawn()
        .unwrap();
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if start.elapsed() > Duration::from_secs(30) {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!(
                "CLI timeout: {extension} {options:?}: {}",
                fs::read_to_string(&stderr).unwrap()
            );
        }
        thread::sleep(Duration::from_millis(20));
    };
    assert!(
        status.success(),
        "{extension} {options:?}: {}",
        fs::read_to_string(&stderr).unwrap()
    );
    serde_json::from_slice(&fs::read(stdout).unwrap()).unwrap()
}

// Use the parser's array abstraction independently of the eager generator to
// compare actual installed terms, not just the generator's hashes or counts.
fn normalize_array_term(raw: &str) -> String {
    use smt2parser::{concrete::Term, vmt::array_abstractor::ArrayAbstractor};
    let mut abstractor = ArrayAbstractor::default();
    for name in ["a".to_string()]
        .into_iter()
        .chain((0..=3).flat_map(|frame| [format!("a@{frame}"), format!("a+{frame}")]))
    {
        abstractor
            .variable_types
            .insert(name, ("Int".into(), "Int".into()));
    }
    raw.parse::<Term>()
        .unwrap()
        .accept(&mut abstractor)
        .unwrap()
        .to_string()
}

fn eager_choices(result: &Value) -> Vec<Value> {
    result["abstract_instantiations"].as_array().unwrap().iter()
        .filter(|record| record["abstract_instantiation_id"].as_str().unwrap().starts_with("eager:"))
        .map(|record| serde_json::json!({
            "id": record["abstract_instantiation_id"],
            "term": normalize_array_term(record["term"].as_str().unwrap()),
            "rule": record["axiom_name"],
            "depth": record["bmc_depth"],
            "substitution": record["substitution"].as_array().unwrap().iter().map(|binding| {
                let mut binding = binding.clone();
                binding["term"] = normalize_array_term(binding["term"].as_str().unwrap()).into();
                binding
            }).collect::<Vec<_>>(),
        })).collect()
}

fn eager_assertions(result: &Value) -> Vec<Value> {
    result["indexed_instantiations"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|record| {
            record["abstract_instantiation_id"]
                .as_str()
                .is_some_and(|id| id.starts_with("eager:"))
        })
        .map(|record| {
            serde_json::json!({
                "id": record["abstract_instantiation_id"],
                "term": normalize_array_term(record["term"].as_str().unwrap()),
                "frame": record["frame"],
                "depth": record["depth"],
            })
        })
        .collect()
}

#[test]
fn concrete_and_abstract_choose_identical_eager_instances_across_costs_and_depths() {
    // Many competing sites and index terms exceed the default 32-instance
    // budget, exercising ranking and tie-breaking rather than selecting all.
    // Syntactic tautologies keep this a selection test even when an experimental
    // cost function is poor at the subsequent CEGAR search.
    let constant_read = "(select ((as const (Array Int Int)) v) j)";
    let mut laws = vec![format!("(= {constant_read} {constant_read})")];
    laws.extend((0..8).map(|offset| {
        format!("(= (select (store a (+ i {offset}) v) j) (select (store a (+ i {offset}) v) j))")
    }));
    let property = format!("(and {})", laws.join(" "));
    for extension in ["vmt", "smt2"] {
        for cost in [
            "bmc-cost",
            "ast-size",
            "adaptive-cost",
            "split-cost",
            "prefer-read",
            "prefer-write",
            "prefer-constants",
            "index-aware",
            "protocol-bmc",
            "generated",
        ] {
            let concrete = run_fixture(
                extension,
                &[
                    "--eager",
                    "--track-instantiations",
                    "-s",
                    "concrete",
                    "-c",
                    cost,
                ],
                &property,
                "3",
            );
            let abstracted = run_fixture(
                extension,
                &[
                    "--eager",
                    "--track-instantiations",
                    "-s",
                    "abstract",
                    "-c",
                    cost,
                ],
                &property,
                "3",
            );
            let expected = eager_choices(&concrete);
            assert_eq!(expected.len(), 32, "one bounded batch for the entire run");
            for result in [&concrete, &abstracted] {
                assert_eq!(result["solver_statistics"]["stats"]["eager.passes"], 1);
                assert!(eager_choices(result)
                    .iter()
                    .all(|record| record["depth"] == 0));
                for frame in 0..if extension == "vmt" { 3 } else { 1 } {
                    assert!(eager_assertions(result)
                        .iter()
                        .any(|record| record["frame"] == frame));
                }
                assert!(eager_assertions(result)
                    .iter()
                    .all(|assertion| expected.iter().any(|seed| seed["id"] == assertion["id"])));
            }
            assert_eq!(eager_choices(&abstracted), expected, "{extension}: {cost}");
            assert!(!eager_assertions(&concrete).is_empty());
            assert_eq!(
                eager_assertions(&abstracted),
                eager_assertions(&concrete),
                "assertions: {extension}: {cost}"
            );
            assert_eq!(abstracted["counterexample"], false);
            assert_eq!(concrete["counterexample"], false);
        }
    }
}

#[test]
fn eager_assertion_parity_with_no_unroll_on_loop() {
    let property = PROPERTY;
    let concrete = run_fixture(
        "vmt",
        &[
            "--eager",
            "--track-instantiations",
            "-s",
            "concrete",
            "--instantiation-strategy",
            "no-unroll-on-loop",
        ],
        property,
        "3",
    );
    let abstracted = run_fixture(
        "vmt",
        &[
            "--eager",
            "--track-instantiations",
            "-s",
            "abstract",
            "--instantiation-strategy",
            "no-unroll-on-loop",
        ],
        property,
        "3",
    );
    assert!(!eager_assertions(&concrete).is_empty());
    assert_eq!(eager_choices(&abstracted), eager_choices(&concrete));
    assert_eq!(eager_assertions(&abstracted), eager_assertions(&concrete));
    for frame in 0..3 {
        assert!(eager_assertions(&concrete)
            .iter()
            .any(|record| record["frame"] == frame));
    }
    assert_eq!(abstracted["total_refinement_steps"], 3);
}

#[test]
fn eager_choices_use_original_source_even_when_abstraction_preprocessing_removes_sites() {
    let read = "(select (store a i v) i)";
    let property = format!("(= {read} {read})");
    for extension in ["vmt", "smt2"] {
        let concrete = run_fixture(extension, &["--eager", "-s", "concrete"], &property, "3");
        let expected = eager_choices(&concrete);
        assert!(!expected.is_empty());
        for strategy in ["abstract", "abstract-with-quantifiers"] {
            let abstracted = run_fixture(
                extension,
                &[
                    "--eager",
                    "-s",
                    strategy,
                    "--preprocess-exact-read-after-write",
                ],
                &property,
                "3",
            );
            assert_eq!(
                eager_choices(&abstracted),
                expected,
                "{extension}: {strategy}"
            );
        }
    }
}

#[test]
fn eager_cli_installs_before_first_check_for_each_array_strategy_and_input_format() {
    for extension in ["vmt", "smt2"] {
        for strategy in ["abstract", "concrete", "abstract-with-quantifiers"] {
            // Default BMC cost exercises the otherwise-simple concrete SMT-LIB dispatch.
            let result = run(extension, &["--eager", "-s", strategy]);
            assert_eq!(result["solver_statistics"]["stats"]["eager.passes"], 1);
            assert!(
                result["solver_statistics"]["stats"]["eager.assertions"]
                    .as_u64()
                    .unwrap()
                    > 0
            );
            assert_eq!(result["total_refinement_steps"], 1);
            assert_eq!(result["counterexample"], false);
            assert!(!result["abstract_instantiations"]
                .as_array()
                .unwrap()
                .is_empty());
        }
        let named = run(extension, &["--eager", "--policy", "german-fast"]);
        assert!(
            named["solver_statistics"]["stats"]["eager.assertions"]
                .as_u64()
                .unwrap()
                > 0
        );
        let cost = run(extension, &["--eager", "-c", "ast-size", "-s", "concrete"]);
        assert!(
            cost["solver_statistics"]["stats"]["eager.assertions"]
                .as_u64()
                .unwrap()
                > 0
        );
    }
}

#[test]
fn eager_cli_is_disabled_by_default() {
    let result = run("vmt", &[]);
    assert!(result["solver_statistics"]["stats"]
        .get("eager.passes")
        .is_none());
    assert!(result["total_refinement_steps"].as_u64().unwrap() > 1);
}

#[test]
fn eager_cli_rejects_incompatible_theory_and_installer() {
    for (options, expected) in [
        (vec!["--eager", "--theory", "list"], "--theory array"),
        (
            vec!["--eager", "--instantiation-strategy", "schema-batch"],
            "model-independent installer",
        ),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
            .args(options)
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains(expected));
    }
}
