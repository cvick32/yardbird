use insta::assert_debug_snapshot;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{
    fs::{self, File},
    path::Path,
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};
use yardbird::{
    self,
    auxiliary_synthesis::AuxSynthesisConfig,
    cost_functions::array::ArrayBMCCost,
    model_from_options,
    smtlib_problem::{SMTLIBProblem, SmtlibCommandExecutor, SmtlibRefinementRunner},
    strategies::{Abstract, ProofStrategy},
    Driver, SolverBackend, YardbirdOptions,
};

#[derive(Debug)]
enum BenchStatus {
    Good,
    Timeout,
    Panic,
}

const CHILD_MODE_ENV: &str = "YARDBIRD_SNAPSHOT_CHILD_MODE";
const CHILD_INPUT_ENV: &str = "YARDBIRD_SNAPSHOT_CHILD_INPUT";
const CHILD_OUTPUT_ENV: &str = "YARDBIRD_SNAPSHOT_CHILD_OUTPUT";

fn run_in_child_process<T>(
    mode: &str,
    input: impl AsRef<Path>,
    timeout: Duration,
) -> (BenchStatus, T)
where
    T: DeserializeOwned + Default,
{
    let directory = tempfile::tempdir().expect("should create child-process result directory");
    let result_path = directory.path().join("result.json");
    let stdout_path = directory.path().join("stdout.log");
    let stderr_path = directory.path().join("stderr.log");
    let executable = std::env::current_exe().expect("should locate snapshot test executable");
    let mut child = Command::new(executable)
        .arg("snapshot_benchmark_child")
        .arg("--exact")
        .env(CHILD_MODE_ENV, mode)
        .env(CHILD_INPUT_ENV, input.as_ref())
        .env(CHILD_OUTPUT_ENV, &result_path)
        .env("RUST_LOG", "off")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .stdout(Stdio::from(
            File::create(&stdout_path).expect("should create child stdout log"),
        ))
        .stderr(Stdio::from(
            File::create(&stderr_path).expect("should create child stderr log"),
        ))
        .spawn()
        .expect("should start snapshot benchmark child");
    let deadline = Instant::now() + timeout;

    loop {
        match child.try_wait() {
            Ok(Some(status)) if status.success() => {
                return match fs::read(&result_path)
                    .ok()
                    .and_then(|bytes| serde_json::from_slice(&bytes).ok())
                {
                    Some(result) => (BenchStatus::Good, result),
                    None => {
                        report_child_failure("wrote no valid result", &stdout_path, &stderr_path);
                        (BenchStatus::Panic, T::default())
                    }
                };
            }
            Ok(Some(status)) => {
                report_child_failure(&format!("exited with {status}"), &stdout_path, &stderr_path);
                return (BenchStatus::Panic, T::default());
            }
            Ok(None) => {}
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                report_child_failure(
                    &format!("could not be polled: {error}"),
                    &stdout_path,
                    &stderr_path,
                );
                return (BenchStatus::Panic, T::default());
            }
        }

        if Instant::now() >= deadline {
            child
                .kill()
                .expect("timed-out snapshot benchmark child should be killable");
            child
                .wait()
                .expect("timed-out snapshot benchmark child should be reaped");
            return (BenchStatus::Timeout, T::default());
        }
        thread::sleep(Duration::from_millis(5));
    }
}

fn report_child_failure(reason: &str, stdout_path: &Path, stderr_path: &Path) {
    let stdout = fs::read_to_string(stdout_path).unwrap_or_default();
    let stderr = fs::read_to_string(stderr_path).unwrap_or_default();
    eprintln!(
        "snapshot benchmark child {reason}\n--- stdout ---\n{stdout}\n--- stderr ---\n{stderr}"
    );
}

#[allow(unused)]
#[derive(Debug)]
struct BenchmarkResult {
    example_name: String,
    status: BenchStatus,
    used_instantiations: Vec<String>,
}

#[allow(unused)]
#[derive(Debug, Default, Deserialize, Serialize)]
struct Smt2StrategyOutcome {
    total_refinement_steps: u32,
    total_instantiations_added: u64,
    found_proof: bool,
    counterexample: bool,
    used_instantiations: Vec<String>,
}

impl From<yardbird::ProofLoopResult> for Smt2StrategyOutcome {
    fn from(result: yardbird::ProofLoopResult) -> Self {
        let mut used_instantiations = result
            .used_instances
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        used_instantiations.sort();

        Self {
            total_refinement_steps: result.total_refinement_steps,
            total_instantiations_added: result.total_instantiations_added,
            found_proof: result.found_proof,
            counterexample: result.counterexample,
            used_instantiations,
        }
    }
}

#[allow(unused)]
#[derive(Debug)]
struct Smt2StrategyResult {
    example_name: String,
    status: BenchStatus,
    outcome: Smt2StrategyOutcome,
}

#[allow(unused)]
#[derive(Debug, Default, Deserialize, Serialize)]
struct Smt2SimpleOutcome {
    results: Vec<String>,
}

#[allow(unused)]
#[derive(Debug)]
struct Smt2SimpleResult {
    example_name: String,
    status: BenchStatus,
    outcome: Smt2SimpleOutcome,
}

#[allow(unused)]
#[derive(Debug)]
struct CliResult {
    status_code: Option<i32>,
    stdout: String,
    stderr: String,
}

fn run_benchmark(filename: impl AsRef<Path>) -> BenchmarkResult {
    let example_name = filename.as_ref().to_string_lossy().to_string();
    let (status, used_instantiations) =
        run_in_child_process("vmt-z3", filename.as_ref(), Duration::from_secs(20));

    BenchmarkResult {
        example_name,
        status,
        used_instantiations,
    }
}

#[cfg(feature = "cvc5-backend")]
fn run_benchmark_with_solver(
    filename: impl AsRef<Path>,
    solver_backend: SolverBackend,
) -> BenchmarkResult {
    let example_name = filename.as_ref().to_string_lossy().to_string();
    let mode = match solver_backend {
        SolverBackend::Z3 => "vmt-z3",
        SolverBackend::Cvc5 => "vmt-cvc5",
    };
    let (status, used_instantiations) =
        run_in_child_process(mode, filename.as_ref(), Duration::from_secs(20));

    BenchmarkResult {
        example_name,
        status,
        used_instantiations,
    }
}

fn run_smt2_strategy_benchmark(filename: impl AsRef<Path>) -> Smt2StrategyResult {
    let example_name = filename.as_ref().to_string_lossy().to_string();
    let (status, outcome) =
        run_in_child_process("smt2-strategy", filename.as_ref(), Duration::from_secs(20));

    Smt2StrategyResult {
        example_name,
        status,
        outcome,
    }
}

fn run_smt2_simple_benchmark(filename: impl AsRef<Path>) -> Smt2SimpleResult {
    let example_name = filename.as_ref().to_string_lossy().to_string();
    let (status, outcome) =
        run_in_child_process("smt2-simple", filename.as_ref(), Duration::from_secs(20));

    Smt2SimpleResult {
        example_name,
        status,
        outcome,
    }
}

fn solve_vmt(filename: &Path, solver_backend: SolverBackend) -> Vec<String> {
    let options = YardbirdOptions::from_filename(filename.to_string_lossy().to_string());
    let vmt_model = model_from_options(&options);
    let instantiation_strategy = options.build_instantiation_strategy();
    let mut driver = Driver::new(vmt_model, instantiation_strategy, solver_backend);
    let strat: Box<dyn ProofStrategy<_>> = Box::new(Abstract::<ArrayBMCCost>::new(
        10,
        false,
        (),
        AuxSynthesisConfig::default(),
        false,
    ));
    let result = driver.check_strategy(options.depth, strat).unwrap();
    let mut used_instantiations = result
        .used_instances
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    used_instantiations.sort();
    used_instantiations
}

fn solve_vmt_with_z3(filename: &Path) -> Vec<String> {
    let path = filename.to_path_buf();
    let mut config = z3::Config::new();
    config.set_model_generation(true);
    z3::with_z3_config(&config, move || solve_vmt(&path, SolverBackend::Z3))
}

fn solve_smt2_strategy(filename: &Path) -> Smt2StrategyOutcome {
    let path = filename.to_path_buf();
    let mut config = z3::Config::new();
    config.set_model_generation(true);

    z3::with_z3_config(&config, move || {
        let problem = SMTLIBProblem::from_path(&path).unwrap();
        let strat: Box<dyn ProofStrategy<_>> = Box::new(Abstract::<ArrayBMCCost>::new(
            0,
            false,
            (),
            AuxSynthesisConfig::default(),
            false,
        ));
        let (result, _abstracted_problem) = SmtlibRefinementRunner::execute(
            &problem,
            strat,
            SolverBackend::Z3,
            250,
            false,
            None,
            None,
        )
        .unwrap();
        Smt2StrategyOutcome::from(result)
    })
}

fn solve_smt2_simple(filename: &Path) -> Smt2SimpleOutcome {
    let path = filename.to_path_buf();
    let mut config = z3::Config::new();
    config.set_model_generation(true);

    z3::with_z3_config(&config, move || {
        let problem = SMTLIBProblem::from_path(&path).unwrap();
        let mut solver = SmtlibCommandExecutor::new(problem.get_logic()).unwrap();
        solver.execute(&problem).unwrap();
        let results = solver
            .get_results()
            .iter()
            .map(|result| format!("{:?}@{}", result.result, result.command_index))
            .collect();
        Smt2SimpleOutcome { results }
    })
}

fn write_child_result(path: &Path, result: &impl Serialize) {
    let bytes = serde_json::to_vec(result).expect("child result should serialize");
    fs::write(path, bytes).expect("child result should be written");
}

#[test]
fn snapshot_benchmark_child() {
    let Some(mode) = std::env::var_os(CHILD_MODE_ENV) else {
        return;
    };
    let input = std::env::var_os(CHILD_INPUT_ENV)
        .map(std::path::PathBuf::from)
        .expect("snapshot child should have an input path");
    let output = std::env::var_os(CHILD_OUTPUT_ENV)
        .map(std::path::PathBuf::from)
        .expect("snapshot child should have an output path");

    match mode.to_string_lossy().as_ref() {
        "vmt-z3" => write_child_result(&output, &solve_vmt_with_z3(&input)),
        "vmt-cvc5" => write_child_result(&output, &solve_vmt(&input, SolverBackend::Cvc5)),
        "smt2-strategy" => write_child_result(&output, &solve_smt2_strategy(&input)),
        "smt2-simple" => write_child_result(&output, &solve_smt2_simple(&input)),
        "timeout-sentinel" => {
            fs::write(input.join("started"), b"").expect("sentinel should report startup");
            thread::sleep(Duration::from_secs(5));
            fs::write(input.join("survived"), b"").expect("sentinel should finish");
            write_child_result(&output, &());
        }
        mode => panic!("unknown snapshot child mode {mode}"),
    }
}

#[test]
fn timed_out_benchmark_work_is_stopped() {
    let directory = tempfile::tempdir().expect("should create sentinel directory");
    let (status, ()): (BenchStatus, ()) =
        run_in_child_process("timeout-sentinel", directory.path(), Duration::from_secs(1));

    assert!(matches!(status, BenchStatus::Timeout));
    assert!(
        directory.path().join("started").exists(),
        "sentinel child should start before the timeout"
    );
    assert!(
        !directory.path().join("survived").exists(),
        "timed-out benchmark process should not continue running"
    );
}

fn run_yardbird_cli(args: &[&str]) -> CliResult {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args(args)
        .env("RUST_LOG", "off")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .unwrap();

    CliResult {
        status_code: output.status.code(),
        stdout: String::from_utf8_lossy(&output.stdout).trim().to_string(),
        stderr: String::from_utf8_lossy(&output.stderr).trim().to_string(),
    }
}

fn benchmark_path(test_name: &str) -> String {
    if test_name.starts_with("array2dim_") {
        format!("examples/two_dimensional_array/{test_name}.vmt")
    } else {
        format!("examples/array/{test_name}.vmt")
    }
}

macro_rules! create_array_snapshot_test {
    ($test:ident) => {
        #[test]
        fn $test() {
            let path = benchmark_path(stringify!($test));
            assert_debug_snapshot!(stringify!($test), run_benchmark(&path));
        }
    };
}

#[test]
fn smt2_array_bitvec_simple_strategy() {
    assert_debug_snapshot!(
        "smt2_array_bitvec_simple_strategy",
        run_smt2_strategy_benchmark("examples/smt2/array_bitvec_simple.smt2")
    );
}

#[test]
#[cfg(feature = "cvc5-backend")]
fn cvc5_vmt_array_copy() {
    assert_debug_snapshot!(
        "cvc5_vmt_array_copy",
        run_benchmark_with_solver("examples/array/array_copy.vmt", SolverBackend::Cvc5)
    );
}

#[test]
fn smt2_array_bitvec_minimal_simple() {
    assert_debug_snapshot!(
        "smt2_array_bitvec_minimal_simple",
        run_smt2_simple_benchmark("examples/smt2/array_bitvec_minimal.smt2")
    );
}

#[test]
fn smt2_auxiliary_synthesis_trigger_rejected() {
    assert_debug_snapshot!(
        "smt2_auxiliary_synthesis_trigger_rejected",
        run_yardbird_cli(&[
            "--filename",
            "examples/smt2/array_bitvec_simple.smt2",
            "--synthesis-trigger",
            "non-local",
        ])
    );
}

fn run_distributed_protocol_depth_2(filename: &str) -> CliResult {
    run_yardbird_cli(&[
        "--filename",
        filename,
        "--depth",
        "2",
        "--strategy",
        "abstract-with-quantifiers",
    ])
}

#[test]
fn distributed_protocol_german_depth_2() {
    assert_debug_snapshot!(
        "distributed_protocol_german_depth_2",
        run_distributed_protocol_depth_2("examples/distributed_protocols/german/german.vmt")
    );
}

#[test]
fn distributed_protocol_flash_coherence_depth_2() {
    assert_debug_snapshot!(
        "distributed_protocol_flash_coherence_depth_2",
        run_distributed_protocol_depth_2(
            "examples/distributed_protocols/flash-coherence/flash-coherence.vmt"
        )
    );
}

// TODO: would be nice to automatically generate this
create_array_snapshot_test!(array2dim_copy);
create_array_snapshot_test!(array2dim_init);
create_array_snapshot_test!(array2dim_init_i);
create_array_snapshot_test!(array2dim_init_j);
create_array_snapshot_test!(array2dim_rec1);
create_array_snapshot_test!(array2dim_rec2);
create_array_snapshot_test!(array_append2_array_horn);
create_array_snapshot_test!(array_bubble_sort);
create_array_snapshot_test!(array_bubble_sort_rev);
create_array_snapshot_test!(array_copy);
create_array_snapshot_test!(array_copy_increment);
create_array_snapshot_test!(array_copy_increment_ind);
create_array_snapshot_test!(array_copy_ind);
create_array_snapshot_test!(array_copy_inverse);
create_array_snapshot_test!(array_copy_nondet_add);
create_array_snapshot_test!(array_copy_sum);
create_array_snapshot_test!(array_copy_sum_ind);
create_array_snapshot_test!(array_doub_access_init);
create_array_snapshot_test!(array_doub_access_init_const);
create_array_snapshot_test!(array_double_inverse);
create_array_snapshot_test!(array_equiv_1);
create_array_snapshot_test!(array_equiv_2);
create_array_snapshot_test!(array_equiv_3);
create_array_snapshot_test!(array_even_odd_1);
create_array_snapshot_test!(array_even_odd_2);
create_array_snapshot_test!(array_horn_copy2);
create_array_snapshot_test!(array_hybr_add);
create_array_snapshot_test!(array_hybr_nest_1);
create_array_snapshot_test!(array_hybr_nest_2);
create_array_snapshot_test!(array_hybr_nest_3);
create_array_snapshot_test!(array_hybr_nest_4);
create_array_snapshot_test!(array_hybr_nest_5);
create_array_snapshot_test!(array_hybr_sum);
create_array_snapshot_test!(array_index_compl);
create_array_snapshot_test!(array_init_addvar);
create_array_snapshot_test!(array_init_addvar2);
create_array_snapshot_test!(array_init_addvar3);
create_array_snapshot_test!(array_init_addvar4);
create_array_snapshot_test!(array_init_addvar5);
create_array_snapshot_test!(array_init_addvar6);
create_array_snapshot_test!(array_init_addvar7);
create_array_snapshot_test!(array_init_and_copy);
create_array_snapshot_test!(array_init_and_copy_const);
create_array_snapshot_test!(array_init_and_copy_inverse);
create_array_snapshot_test!(array_init_batches);
create_array_snapshot_test!(array_init_batches_const);
create_array_snapshot_test!(array_init_batches_ind);
create_array_snapshot_test!(array_init_both_ends);
create_array_snapshot_test!(array_init_both_ends2);
create_array_snapshot_test!(array_init_both_ends_multiple);
create_array_snapshot_test!(array_init_both_ends_multiple_sum);
create_array_snapshot_test!(array_init_both_ends_simpl);
create_array_snapshot_test!(array_init_both_ends_simpl_const);
create_array_snapshot_test!(array_init_const);
create_array_snapshot_test!(array_init_const_const);
create_array_snapshot_test!(array_init_const_ind);
create_array_snapshot_test!(array_init_depend);
create_array_snapshot_test!(array_init_depend_incr);
create_array_snapshot_test!(array_init_disj);
create_array_snapshot_test!(array_init_disj_const);
create_array_snapshot_test!(array_init_doubl);
create_array_snapshot_test!(array_init_doubl2);
create_array_snapshot_test!(array_init_doubl3);
create_array_snapshot_test!(array_init_double);
create_array_snapshot_test!(array_init_double_const);
create_array_snapshot_test!(array_init_drop);
create_array_snapshot_test!(array_init_increm);
create_array_snapshot_test!(array_init_increm_const);
create_array_snapshot_test!(array_init_increm_twice);
create_array_snapshot_test!(array_init_increm_twice_const);
create_array_snapshot_test!(array_init_increm_two_arrs);
create_array_snapshot_test!(array_init_increm_two_arrs_antisym);
create_array_snapshot_test!(array_init_increm_two_arrs_antisym_const);
create_array_snapshot_test!(array_init_increm_two_arrs_const);
create_array_snapshot_test!(array_init_ite);
create_array_snapshot_test!(array_init_ite_dupl);
create_array_snapshot_test!(array_init_ite_jump);
create_array_snapshot_test!(array_init_ite_jump_const);
create_array_snapshot_test!(array_init_ite_jump_two);
create_array_snapshot_test!(array_init_ite_jump_two_const);
create_array_snapshot_test!(array_init_monot_ind);
create_array_snapshot_test!(array_init_nondet_var_mult);
create_array_snapshot_test!(array_init_nondet_vars);
create_array_snapshot_test!(array_init_nondet_vars2);
create_array_snapshot_test!(array_init_nondet_vars_plus_ind);
create_array_snapshot_test!(array_init_pair_sum);
create_array_snapshot_test!(array_init_pair_sum_const);
create_array_snapshot_test!(array_init_pair_symmetr);
create_array_snapshot_test!(array_init_pair_symmetr2);
create_array_snapshot_test!(array_init_pair_symmetr3);
create_array_snapshot_test!(array_init_pair_symmetr4);
create_array_snapshot_test!(array_init_reverse);
create_array_snapshot_test!(array_init_reverse_const);
create_array_snapshot_test!(array_init_reverse_mult);
create_array_snapshot_test!(array_init_select);
create_array_snapshot_test!(array_init_select_copy);
create_array_snapshot_test!(array_init_symmetr_swap);
create_array_snapshot_test!(array_init_symmetr_swap_const);
create_array_snapshot_test!(array_init_tuples);
create_array_snapshot_test!(array_init_tuples_relative);
create_array_snapshot_test!(array_init_upto_nondet);
create_array_snapshot_test!(array_init_var);
create_array_snapshot_test!(array_init_var_ind);
create_array_snapshot_test!(array_init_var_plus_ind);
create_array_snapshot_test!(array_init_var_plus_ind2);
create_array_snapshot_test!(array_init_var_plus_ind3);
create_array_snapshot_test!(array_max_min);
create_array_snapshot_test!(array_max_min_approx);
create_array_snapshot_test!(array_max_min_shift);
create_array_snapshot_test!(array_max_reverse_min);
create_array_snapshot_test!(array_min);
create_array_snapshot_test!(array_min_and_copy);
create_array_snapshot_test!(array_min_and_copy_inverse);
create_array_snapshot_test!(array_min_and_copy_shift);
create_array_snapshot_test!(array_min_and_copy_shift_sum);
create_array_snapshot_test!(array_min_and_copy_shift_sum_add);
create_array_snapshot_test!(array_min_const);
create_array_snapshot_test!(array_min_ind);
create_array_snapshot_test!(array_min_max);
create_array_snapshot_test!(array_min_max_const);
create_array_snapshot_test!(array_min_swap);
create_array_snapshot_test!(array_min_swap_and_shift);
create_array_snapshot_test!(array_min_swap_const);
create_array_snapshot_test!(array_nest_split_01);
create_array_snapshot_test!(array_nest_split_02);
create_array_snapshot_test!(array_nest_split_03);
create_array_snapshot_test!(array_nest_split_04);
create_array_snapshot_test!(array_nest_split_05);
create_array_snapshot_test!(array_nonlin_init_depend);
create_array_snapshot_test!(array_nonlin_init_mult);
create_array_snapshot_test!(array_nonlin_square);
create_array_snapshot_test!(array_partial_init);
create_array_snapshot_test!(array_single_elem);
create_array_snapshot_test!(array_single_elem_const);
create_array_snapshot_test!(array_single_elem_increm);
create_array_snapshot_test!(array_split_01);
create_array_snapshot_test!(array_split_02);
create_array_snapshot_test!(array_split_03);
create_array_snapshot_test!(array_split_04);
create_array_snapshot_test!(array_split_05);
create_array_snapshot_test!(array_split_06);
create_array_snapshot_test!(array_split_07);
create_array_snapshot_test!(array_split_08);
create_array_snapshot_test!(array_split_09);
create_array_snapshot_test!(array_split_10);
create_array_snapshot_test!(array_split_11);
create_array_snapshot_test!(array_split_12);
create_array_snapshot_test!(array_split_13);
create_array_snapshot_test!(array_split_14);
create_array_snapshot_test!(array_split_15);
create_array_snapshot_test!(array_split_16);
create_array_snapshot_test!(array_split_17);
create_array_snapshot_test!(array_split_18);
create_array_snapshot_test!(array_split_19);
create_array_snapshot_test!(array_split_20);
create_array_snapshot_test!(array_split_21);
create_array_snapshot_test!(array_standard_copy4);
create_array_snapshot_test!(array_standard_partition);
create_array_snapshot_test!(array_standard_password);
create_array_snapshot_test!(array_tiling_pnr2);
create_array_snapshot_test!(array_tiling_pnr3);
create_array_snapshot_test!(array_tiling_pnr4);
create_array_snapshot_test!(array_tiling_pnr5);
create_array_snapshot_test!(array_tiling_poly1);
create_array_snapshot_test!(array_tiling_poly2);
create_array_snapshot_test!(array_tiling_poly3);
create_array_snapshot_test!(array_tiling_poly4);
create_array_snapshot_test!(array_tiling_poly5);
create_array_snapshot_test!(array_tiling_poly6);
create_array_snapshot_test!(array_tiling_pr2);
create_array_snapshot_test!(array_tiling_pr3);
create_array_snapshot_test!(array_tiling_pr4);
create_array_snapshot_test!(array_tiling_pr5);
create_array_snapshot_test!(array_tiling_rew);
create_array_snapshot_test!(array_tiling_rewnif);
create_array_snapshot_test!(array_tiling_rewnifrev);
create_array_snapshot_test!(array_tiling_rewnifrev2);
create_array_snapshot_test!(array_tiling_rewrev);
create_array_snapshot_test!(array_tiling_skipped);
create_array_snapshot_test!(array_tiling_tcpy);
create_array_snapshot_test!(array_tiling_tcpy2);
create_array_snapshot_test!(array_tiling_tcpy3);
create_array_snapshot_test!(array_tripl_access_init);
create_array_snapshot_test!(array_tripl_access_init_const);
create_array_snapshot_test!(array_two_counters_add);
create_array_snapshot_test!(array_two_counters_init_const);
create_array_snapshot_test!(array_two_counters_init_var);
create_array_snapshot_test!(array_two_counters_max_subtr);
create_array_snapshot_test!(array_two_counters_min_max);
create_array_snapshot_test!(array_two_counters_min_max_prog);
create_array_snapshot_test!(array_two_counters_replace);
create_array_snapshot_test!(array_two_counters_sum);
create_array_snapshot_test!(array_zero_sum_m2);
