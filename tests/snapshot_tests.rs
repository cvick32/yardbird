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
    cost_functions::array::ArrayBMCCost,
    model_from_options,
    smtlib_problem::{SMTLIBProblem, SmtlibCommandExecutor, SmtlibRefinementRunner},
    strategies::{Abstract, ProofStrategy},
    Driver, Error, SolverBackend, Strategy, YardbirdOptions,
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
const CHILD_CONFIG_ENV: &str = "YARDBIRD_SNAPSHOT_CHILD_CONFIG";

fn run_in_child_process<T>(
    mode: &str,
    input: impl AsRef<Path>,
    timeout: Duration,
) -> (BenchStatus, T)
where
    T: DeserializeOwned + Default,
{
    run_in_child_process_with_env(mode, input, timeout, &[])
}

fn run_in_child_process_with_env<T>(
    mode: &str,
    input: impl AsRef<Path>,
    timeout: Duration,
    environment: &[(&str, String)],
) -> (BenchStatus, T)
where
    T: DeserializeOwned + Default,
{
    let directory = tempfile::tempdir().expect("should create child-process result directory");
    let result_path = directory.path().join("result.json");
    let stdout_path = directory.path().join("stdout.log");
    let stderr_path = directory.path().join("stderr.log");
    let executable = std::env::current_exe().expect("should locate snapshot test executable");
    let mut command = Command::new(executable);
    command
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
        ));
    for (key, value) in environment {
        command.env(key, value);
    }
    let mut child = command
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

#[derive(Copy, Clone, Debug, Deserialize, Serialize)]
struct VmtSnapshotConfig {
    strategy: Strategy,
    solver: SolverBackend,
    target_depth: u16,
}

impl VmtSnapshotConfig {
    fn concrete(target_depth: u16) -> Self {
        Self {
            strategy: Strategy::Concrete,
            solver: SolverBackend::Z3,
            target_depth,
        }
    }
}

#[derive(Debug, Default, Deserialize, Serialize)]
enum VmtSnapshotOutcome {
    BoundedSafe {
        solver_checks: u32,
    },
    Counterexample,
    SolverUnknown {
        reason: Option<String>,
    },
    YardbirdError {
        message: String,
    },
    #[default]
    MissingChildResult,
}

#[allow(dead_code)]
#[derive(Debug)]
struct VmtSnapshotResult {
    example_name: String,
    config: VmtSnapshotConfig,
    outcome: VmtSnapshotOutcome,
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
    let strat: Box<dyn ProofStrategy<_>> =
        Box::new(Abstract::<ArrayBMCCost>::new(10, false, (), false));
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

fn solve_vmt_snapshot(filename: &Path, config: VmtSnapshotConfig) -> VmtSnapshotOutcome {
    let mut options = YardbirdOptions::from_filename(filename.to_string_lossy().to_string());
    options.depth = config.target_depth;
    options.strategy = config.strategy;
    options.solver = config.solver;
    let vmt_model = model_from_options(&options);
    let instantiation_strategy = options.build_instantiation_strategy();
    let mut driver = Driver::new(vmt_model, instantiation_strategy, config.solver);

    match driver.check_strategy(options.depth, options.build_array_strategy()) {
        Ok(result) => VmtSnapshotOutcome::BoundedSafe {
            solver_checks: result.total_refinement_steps,
        },
        Err(Error::Counterexample) => VmtSnapshotOutcome::Counterexample,
        Err(Error::SolverUnknown(reason)) => VmtSnapshotOutcome::SolverUnknown { reason },
        Err(error) => VmtSnapshotOutcome::YardbirdError {
            message: error.to_string(),
        },
    }
}

fn run_vmt_snapshot_benchmark(
    filename: impl AsRef<Path>,
    config: VmtSnapshotConfig,
) -> VmtSnapshotResult {
    let example_name = filename.as_ref().to_string_lossy().to_string();
    let serialized_config =
        serde_json::to_string(&config).expect("snapshot configuration should serialize");
    let (status, outcome) = run_in_child_process_with_env(
        "vmt-snapshot",
        filename.as_ref(),
        Duration::from_secs(20),
        &[(CHILD_CONFIG_ENV, serialized_config)],
    );

    match status {
        BenchStatus::Good => {}
        BenchStatus::Timeout => panic!("snapshot benchmark timed out: {example_name}"),
        BenchStatus::Panic => panic!("snapshot benchmark child failed: {example_name}"),
    }

    VmtSnapshotResult {
        example_name,
        config,
        outcome,
    }
}

fn solve_smt2_strategy(filename: &Path) -> Smt2StrategyOutcome {
    let path = filename.to_path_buf();
    let mut config = z3::Config::new();
    config.set_model_generation(true);

    z3::with_z3_config(&config, move || {
        let problem = SMTLIBProblem::from_path(&path).unwrap();
        let strat: Box<dyn ProofStrategy<_>> =
            Box::new(Abstract::<ArrayBMCCost>::new(0, false, (), false));
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
        "vmt-snapshot" => {
            let config = std::env::var(CHILD_CONFIG_ENV)
                .expect("snapshot child should have a configuration");
            let config: VmtSnapshotConfig =
                serde_json::from_str(&config).expect("snapshot child configuration should parse");
            let outcome = if config.solver == SolverBackend::Z3 {
                let path = input.clone();
                let mut z3_config = z3::Config::new();
                z3_config.set_model_generation(true);
                z3::with_z3_config(&z3_config, move || solve_vmt_snapshot(&path, config))
            } else {
                solve_vmt_snapshot(&input, config)
            };
            write_child_result(&output, &outcome);
        }
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

#[test]
fn concrete_snapshot_runner_reports_each_checked_depth() {
    let result = run_vmt_snapshot_benchmark(
        "examples/array/array_copy.vmt",
        VmtSnapshotConfig::concrete(1),
    );

    assert!(matches!(
        result.outcome,
        VmtSnapshotOutcome::BoundedSafe { solver_checks: 1 }
    ));
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

fn collect_benchmark_paths(root: &Path, extension: &str) -> Vec<String> {
    fn visit(directory: &Path, root: &Path, extension: &str, paths: &mut Vec<String>) {
        for entry in fs::read_dir(directory).expect("snapshot suite directory should be readable") {
            let entry = entry.expect("snapshot suite entry should be readable");
            let path = entry.path();
            if path.is_dir() {
                visit(&path, root, extension, paths);
            } else if path.extension().and_then(|value| value.to_str()) == Some(extension) {
                let relative = path
                    .strip_prefix(root)
                    .expect("discovered benchmark should be below the suite root")
                    .to_string_lossy()
                    .replace(std::path::MAIN_SEPARATOR, "/");
                paths.push(relative);
            }
        }
    }

    let mut paths = Vec::new();
    visit(root, root, extension, &mut paths);
    paths.sort();
    paths
}

macro_rules! snapshot_suite {
    (
        root: $root:literal,
        extension: $extension:literal,
        inventory: $inventory:ident,
        exclude: {$($excluded_path:literal => $reason:literal),* $(,)?},
        runner: $runner:path,
        accept: $accept:path,
        cases: {
            $($case:ident $(=> $relative_path:literal)?),* $(,)?
        }
    ) => {
        $(
            #[test]
            fn $case() {
                let path = Path::new($root).join(snapshot_suite!(
                    @relative_path $case $(, $relative_path)?
                ));
                let result = $runner(&path);
                $accept(&result);
                assert_debug_snapshot!(stringify!($case), result);
            }
        )*

        snapshot_suite! {
            @inventory
            root: $root,
            extension: $extension,
            inventory: $inventory,
            exclude: {$($excluded_path => $reason),*},
            cases: {$($case $(=> $relative_path)?),*}
        }
    };
    (
        root: $root:literal,
        extension: $extension:literal,
        inventory: $inventory:ident,
        exclude: {$($excluded_path:literal => $reason:literal),* $(,)?},
        runner: $runner:path,
        cases: {
            $($case:ident $(=> $relative_path:literal)?),* $(,)?
        }
    ) => {
        $(
            #[test]
            fn $case() {
                let path = Path::new($root).join(snapshot_suite!(
                    @relative_path $case $(, $relative_path)?
                ));
                assert_debug_snapshot!(stringify!($case), $runner(&path));
            }
        )*

        snapshot_suite! {
            @inventory
            root: $root,
            extension: $extension,
            inventory: $inventory,
            exclude: {$($excluded_path => $reason),*},
            cases: {$($case $(=> $relative_path)?),*}
        }
    };
    (
        @inventory
        root: $root:literal,
        extension: $extension:literal,
        inventory: $inventory:ident,
        exclude: {$($excluded_path:literal => $reason:literal),* $(,)?},
        cases: {$($case:ident $(=> $relative_path:literal)?),* $(,)?}
    ) => {
        #[test]
        fn $inventory() {
            let mut covered = vec![$(
                snapshot_suite!(@relative_path $case $(, $relative_path)?).to_string()
            ),*];
            let declared_count = covered.len();
            $(
                assert!(!$reason.is_empty(), "snapshot suite exclusions require a reason");
                covered.push($excluded_path.to_string());
            )*
            covered.sort();
            covered.dedup();

            assert_eq!(
                covered.len(),
                declared_count + snapshot_suite!(@count $($excluded_path),*),
                "snapshot suite paths must be unique"
            );
            let discovered = collect_benchmark_paths(Path::new($root), $extension);

            assert_eq!(covered, discovered, "snapshot suite declaration is out of sync");
        }
    };
    (@relative_path $case:ident, $relative_path:literal) => {
        $relative_path
    };
    (@relative_path $case:ident) => {
        concat!(stringify!($case), ".vmt")
    };
    (@count $($item:literal),*) => {
        <[()]>::len(&[$(snapshot_suite!(@replace $item)),*])
    };
    (@replace $item:literal) => { () };
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

mod concrete_distributed_protocols_depth_5 {
    use super::*;

    snapshot_suite! {
        root: "examples/distributed_protocols",
        extension: "vmt",
        inventory: every_distributed_protocol_has_a_snapshot_test,
        exclude: {},
        runner: run_concrete_protocol,
        accept: assert_bounded_safe,
        cases: {
            chord_ring_maintenance => "chord_ring_maintenance/chord_ring_maintenance.vmt",
            client_server_ae => "client_server_ae/client_server_ae.vmt",
            client_server_db_ae => "client_server_db_ae/client_server_db_ae.vmt",
            consensus_epr => "consensus_epr/consensus_epr.vmt",
            consensus_forall => "consensus_forall/consensus_forall.vmt",
            consensus_wo_decide => "consensus_wo_decide/consensus_wo_decide.vmt",
            database_chain_replication => "database_chain_replication/database_chain_replication.vmt",
            decentralized_lock => "decentralized_lock/decentralized_lock.vmt",
            distributed_lock => "distributed_lock/distributed_lock.vmt",
            fast_paxos => "fast_paxos/fast_paxos.vmt",
            flash_coherence => "flash-coherence/flash-coherence.vmt",
            flexible_paxos => "flexible_paxos/flexible_paxos.vmt",
            german => "german/german.vmt",
            hybrid_reliable_broadcast => "hybrid_reliable_broadcast/hybrid_reliable_broadcast.vmt",
            learning_switch_quad => "learning_switch_quad/learning_switch_quad.vmt",
            learning_switch_ternary => "learning_switch_ternary/learning_switch_ternary.vmt",
            lock_server_async => "lock_server_async/lock_server_async.vmt",
            lock_server_sync => "lock_server_sync/lock_server_sync.vmt",
            multi_paxos => "multi_paxos/multi_paxos.vmt",
            paxos => "paxos/paxos.vmt",
            ring_leader_election => "ring_leader_election/ring_leader_election.vmt",
            sharded_key_value_store => "sharded_key_value_store/sharded_key_value_store.vmt",
            sharded_kv_no_lost_keys => "sharded_kv_no_lost_keys/sharded_kv_no_lost_keys.vmt",
            stoppable_paxos => "stoppable_paxos/stoppable_paxos.vmt",
            ticket_lock => "ticket_lock/ticket_lock.vmt",
            tomasulo => "tomasulo/tomasulo.vmt",
            toy_consensus_epr => "toy_consensus_epr/toy_consensus_epr.vmt",
            toy_consensus_forall => "toy_consensus_forall/toy_consensus_forall.vmt",
            two_phase_commit => "two_phase_commit/two_phase_commit.vmt",
            vertical_paxos => "vertical_paxos/vertical_paxos.vmt",
        }
    }

    fn run_concrete_protocol(path: &Path) -> VmtSnapshotResult {
        run_vmt_snapshot_benchmark(path, VmtSnapshotConfig::concrete(5))
    }

    fn assert_bounded_safe(result: &VmtSnapshotResult) {
        assert!(
            matches!(
                result.outcome,
                VmtSnapshotOutcome::BoundedSafe { solver_checks: 5 }
            ),
            "concrete protocol did not complete depths 0-4: {result:#?}"
        );
    }
}

snapshot_suite! {
    root: "examples/two_dimensional_array",
    extension: "vmt",
    inventory: every_two_dimensional_array_benchmark_has_a_snapshot_test,
    exclude: {},
    runner: run_benchmark,
    cases: {
        array2dim_copy,
        array2dim_init,
        array2dim_init_i,
        array2dim_init_j,
        array2dim_rec1,
        array2dim_rec2,
    }
}

snapshot_suite! {
    root: "examples/array",
    extension: "vmt",
    inventory: every_array_benchmark_is_declared,
    exclude: {
        "array_scatter.vmt" => "legacy suite has no accepted snapshot for this research fixture",
        "array_scatter_instrumented.vmt" => "legacy suite has no accepted snapshot for this instrumented research fixture",
    },
    runner: run_benchmark,
    cases: {
        array_append2_array_horn,
        array_bubble_sort,
        array_bubble_sort_rev,
        array_copy,
        array_copy_increment,
        array_copy_increment_ind,
        array_copy_ind,
        array_copy_inverse,
        array_copy_nondet_add,
        array_copy_sum,
        array_copy_sum_ind,
        array_doub_access_init,
        array_doub_access_init_const,
        array_double_inverse,
        array_equiv_1,
        array_equiv_2,
        array_equiv_3,
        array_even_odd_1,
        array_even_odd_2,
        array_horn_copy2,
        array_hybr_add,
        array_hybr_nest_1,
        array_hybr_nest_2,
        array_hybr_nest_3,
        array_hybr_nest_4,
        array_hybr_nest_5,
        array_hybr_sum,
        array_index_compl,
        array_init_addvar,
        array_init_addvar2,
        array_init_addvar3,
        array_init_addvar4,
        array_init_addvar5,
        array_init_addvar6,
        array_init_addvar7,
        array_init_and_copy,
        array_init_and_copy_const,
        array_init_and_copy_inverse,
        array_init_batches,
        array_init_batches_const,
        array_init_batches_ind,
        array_init_both_ends,
        array_init_both_ends2,
        array_init_both_ends_multiple,
        array_init_both_ends_multiple_sum,
        array_init_both_ends_simpl,
        array_init_both_ends_simpl_const,
        array_init_const,
        array_init_const_const,
        array_init_const_ind,
        array_init_depend,
        array_init_depend_incr,
        array_init_disj,
        array_init_disj_const,
        array_init_doubl,
        array_init_doubl2,
        array_init_doubl3,
        array_init_double,
        array_init_double_const,
        array_init_drop,
        array_init_increm,
        array_init_increm_const,
        array_init_increm_twice,
        array_init_increm_twice_const,
        array_init_increm_two_arrs,
        array_init_increm_two_arrs_antisym,
        array_init_increm_two_arrs_antisym_const,
        array_init_increm_two_arrs_const,
        array_init_ite,
        array_init_ite_dupl,
        array_init_ite_jump,
        array_init_ite_jump_const,
        array_init_ite_jump_two,
        array_init_ite_jump_two_const,
        array_init_monot_ind,
        array_init_nondet_var_mult,
        array_init_nondet_vars,
        array_init_nondet_vars2,
        array_init_nondet_vars_plus_ind,
        array_init_pair_sum,
        array_init_pair_sum_const,
        array_init_pair_symmetr,
        array_init_pair_symmetr2,
        array_init_pair_symmetr3,
        array_init_pair_symmetr4,
        array_init_reverse,
        array_init_reverse_const,
        array_init_reverse_mult,
        array_init_select,
        array_init_select_copy,
        array_init_symmetr_swap,
        array_init_symmetr_swap_const,
        array_init_tuples,
        array_init_tuples_relative,
        array_init_upto_nondet,
        array_init_var,
        array_init_var_ind,
        array_init_var_plus_ind,
        array_init_var_plus_ind2,
        array_init_var_plus_ind3,
        array_max_min,
        array_max_min_approx,
        array_max_min_shift,
        array_max_reverse_min,
        array_min,
        array_min_and_copy,
        array_min_and_copy_inverse,
        array_min_and_copy_shift,
        array_min_and_copy_shift_sum,
        array_min_and_copy_shift_sum_add,
        array_min_const,
        array_min_ind,
        array_min_max,
        array_min_max_const,
        array_min_swap,
        array_min_swap_and_shift,
        array_min_swap_const,
        array_nest_split_01,
        array_nest_split_02,
        array_nest_split_03,
        array_nest_split_04,
        array_nest_split_05,
        array_nonlin_init_depend,
        array_nonlin_init_mult,
        array_nonlin_square,
        array_partial_init,
        array_single_elem,
        array_single_elem_const,
        array_single_elem_increm,
        array_split_01,
        array_split_02,
        array_split_03,
        array_split_04,
        array_split_05,
        array_split_06,
        array_split_07,
        array_split_08,
        array_split_09,
        array_split_10,
        array_split_11,
        array_split_12,
        array_split_13,
        array_split_14,
        array_split_15,
        array_split_16,
        array_split_17,
        array_split_18,
        array_split_19,
        array_split_20,
        array_split_21,
        array_standard_copy4,
        array_standard_partition,
        array_standard_password,
        array_tiling_pnr2,
        array_tiling_pnr3,
        array_tiling_pnr4,
        array_tiling_pnr5,
        array_tiling_poly1,
        array_tiling_poly2,
        array_tiling_poly3,
        array_tiling_poly4,
        array_tiling_poly5,
        array_tiling_poly6,
        array_tiling_pr2,
        array_tiling_pr3,
        array_tiling_pr4,
        array_tiling_pr5,
        array_tiling_rew,
        array_tiling_rewnif,
        array_tiling_rewnifrev,
        array_tiling_rewnifrev2,
        array_tiling_rewrev,
        array_tiling_skipped,
        array_tiling_tcpy,
        array_tiling_tcpy2,
        array_tiling_tcpy3,
        array_tripl_access_init,
        array_tripl_access_init_const,
        array_two_counters_add,
        array_two_counters_init_const,
        array_two_counters_init_var,
        array_two_counters_max_subtr,
        array_two_counters_min_max,
        array_two_counters_min_max_prog,
        array_two_counters_replace,
        array_two_counters_sum,
        array_zero_sum_m2,
    }
}
