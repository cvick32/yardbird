use anyhow::anyhow;
use chrono::{DateTime, Utc};
use clap::Parser;
use glob::Pattern;
use serde::Serialize;
use std::{
    collections::HashSet,
    fs::{self, OpenOptions},
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::{
        atomic::{AtomicUsize, Ordering},
        mpsc, Arc,
    },
    thread,
    time::{Duration, Instant},
};
use yardbird::{
    auxiliary_synthesis::{GuardPolicy, SynthesisTrigger},
    ProofLoopResult, YardbirdOptions,
};

mod config;
use config::BenchmarkConfig;

#[derive(Parser, Debug, Clone)]
#[command(version, about, long_about = None)]
struct GardenOptions {
    #[arg(short, long)]
    pub config: Option<PathBuf>,

    #[arg(short, long)]
    pub matrix: Option<String>,

    pub examples: Option<PathBuf>,

    #[arg(short, long)]
    pub depth: Option<u16>,

    #[arg(short, long)]
    pub timeout: Option<u64>,

    /// Maximum number of benchmarks to run after filtering.
    #[arg(long)]
    pub limit: Option<usize>,

    /// Seed for deterministic benchmark sampling when a limit is set.
    #[arg(long)]
    pub sample_seed: Option<u64>,

    /// Only run VMT benchmarks containing at least one array read and one array write.
    #[arg(long, default_value_t = false)]
    pub require_array_reads_and_writes: bool,

    /// Number of Yardbird subprocesses to run concurrently.
    #[arg(long)]
    pub jobs: Option<usize>,

    #[arg(short, long)]
    pub include: Vec<String>,

    #[arg(long, default_value_t = false)]
    pub run_ic3ia: bool,

    #[arg(short, long)]
    pub skip: Vec<String>,

    #[arg(short, long)]
    pub output: Option<PathBuf>,

    #[arg(short, long)]
    pub pretty: bool,

    #[arg(long)]
    pub strategy: Vec<yardbird::Strategy>,

    #[arg(long)]
    pub retry: Option<usize>,

    #[arg(long)]
    pub cost_function: Option<yardbird::CostFunction>,

    #[arg(long, value_enum, default_value_t = yardbird::EGraphBuilderStrategy::Full)]
    pub egraph_builder: yardbird::EGraphBuilderStrategy,

    #[arg(long, value_enum, default_value_t = yardbird::SolverBackend::Z3)]
    pub solver: yardbird::SolverBackend,

    #[arg(long, default_value_t = false)]
    pub train: bool,

    #[arg(long)]
    pub ranker_model: Option<String>,

    #[arg(long, default_value_t = false)]
    pub profile: bool,

    /// Capture each Yardbird solver session beneath this directory.
    #[arg(long)]
    pub solver_capture_root: Option<PathBuf>,

    #[arg(long, default_value_t = false)]
    pub record_decisions: bool,

    #[arg(long)]
    pub database_url: Option<String>,

    #[arg(long, default_value_t = false)]
    pub track_instantiations: bool,

    #[arg(long)]
    pub training_run_version: Option<String>,

    #[arg(long, value_enum, default_value_t = SynthesisTrigger::Off)]
    pub synthesis_trigger: SynthesisTrigger,

    #[arg(long, value_enum, default_value_t = GuardPolicy::True)]
    pub synthesis_guard_policy: GuardPolicy,

    #[arg(long)]
    pub synthesis_after: Option<u32>,

    #[arg(long)]
    pub synthesis_refinement_limit_window: Option<u32>,

    #[arg(long)]
    pub synthesis_repeated_pattern_threshold: Option<u32>,
}

#[derive(Debug, Serialize)]
enum BenchmarkResult {
    Success(ProofLoopResult),
    _FoundProof(ProofLoopResult),
    NoProgress(ProofLoopResult),
    Timeout(u128),
    Error(String),
}

#[derive(Debug, Serialize)]
struct Benchmark {
    example: String,
    result: Vec<StrategyResult>,
}

#[derive(Debug, Serialize)]
struct BenchmarkSuite {
    metadata: SuiteMetadata,
    benchmarks: Vec<Benchmark>,
}

#[derive(Debug, Serialize)]
struct SuiteMetadata {
    timestamp: DateTime<Utc>,
    git_commit: Option<String>,
    config_name: Option<String>,
    total_benchmarks: usize,
    yardbird_version: String,
}

#[derive(Debug, Serialize)]
struct StrategyResult {
    solver: yardbird::SolverBackend,
    strategy: yardbird::Strategy,
    cost_function: yardbird::CostFunction,
    egraph_builder: yardbird::EGraphBuilderStrategy,
    result: BenchmarkResult,
    run_time: u128,
    depth: u16,
    record_decisions: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    solver_capture_dir: Option<PathBuf>,
}

fn default_training_run_version() -> String {
    format!(
        "garden-training-{}-pid{}",
        Utc::now().format("%Y%m%d_%H%M%S"),
        std::process::id()
    )
}

fn effective_training_run_version(options: &GardenOptions) -> Option<String> {
    if !options.train {
        return None;
    }

    Some(
        options
            .training_run_version
            .clone()
            .unwrap_or_else(default_training_run_version),
    )
}

fn read_pipe_in_background<R>(mut pipe: R) -> thread::JoinHandle<String>
where
    R: Read + Send + 'static,
{
    thread::spawn(move || {
        let mut output = String::new();
        let _ = pipe.read_to_string(&mut output);
        output
    })
}

fn collect_reader(reader: &mut Option<thread::JoinHandle<String>>) -> String {
    reader
        .take()
        .and_then(|reader| reader.join().ok())
        .unwrap_or_default()
}

fn run_yardbird_subprocess(options: &YardbirdOptions, timeout: Duration) -> BenchmarkResult {
    // Get the path to the yardbird binary (in target/release/)
    let yardbird_bin = std::env::current_exe()
        .ok()
        .and_then(|p| p.parent().map(|p| p.to_path_buf()))
        .map(|mut p| {
            p.push("yardbird");
            p
        })
        .expect("Failed to find yardbird binary path");

    let filename = options
        .filename
        .as_deref()
        .expect("garden only spawns yardbird with a filename");

    // Build command line arguments for yardbird with JSON output
    let mut command = Command::new(&yardbird_bin);
    command
        .arg("--filename")
        .arg(filename)
        .arg("--depth")
        .arg(options.depth.to_string())
        .arg("--strategy")
        .arg(options.strategy.to_string())
        .arg("--cost-function")
        .arg(options.cost_function.to_string())
        .arg("--egraph-builder")
        .arg(options.egraph_builder.to_string())
        .arg("--solver")
        .arg(options.solver.to_string())
        .arg("--synthesis-trigger")
        .arg(options.synthesis_trigger.to_string())
        .arg("--synthesis-guard-policy")
        .arg(options.synthesis_guard_policy.to_string())
        .arg("--json-output");

    if options.run_ic3ia {
        command.arg("--run-ic3ia");
    }

    if let Some(synthesis_after) = options.synthesis_after {
        command
            .arg("--synthesis-after")
            .arg(synthesis_after.to_string());
    }

    if let Some(window) = options.synthesis_refinement_limit_window {
        command
            .arg("--synthesis-refinement-limit-window")
            .arg(window.to_string());
    }

    if let Some(threshold) = options.synthesis_repeated_pattern_threshold {
        command
            .arg("--synthesis-repeated-pattern-threshold")
            .arg(threshold.to_string());
    }

    if options.train {
        command.arg("--train");
    }

    if options.track_instantiations {
        command.arg("--track-instantiations");
    }

    if options.profile {
        command.arg("--profile");
    }

    if let Some(capture_dir) = &options.solver_capture_dir {
        command.arg("--solver-capture-dir").arg(capture_dir);
    }

    if options.record_decisions {
        command.arg("--record-decisions");
    }

    if matches!(
        options.cost_function,
        yardbird::CostFunction::LogisticRegression
    ) {
        if let Some(ranker_model) = &options.ranker_model {
            command.arg("--ranker-model").arg(ranker_model);
        }
    }

    if let Some(database_url) = &options.database_url {
        command.arg("--database-url").arg(database_url);
    }

    if let Some(training_run_version) = &options.training_run_version {
        command
            .arg("--training-run-version")
            .arg(training_run_version);
    }

    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn yardbird subprocess");

    let mut stdout_reader = child.stdout.take().map(read_pipe_in_background);
    let mut stderr_reader = child.stderr.take().map(read_pipe_in_background);
    let pid = child.id();
    let start = Instant::now();

    // Poll the subprocess until it completes or times out
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                // Process completed, collect output that was drained while it ran.
                let stdout = collect_reader(&mut stdout_reader);
                let stderr = collect_reader(&mut stderr_reader);

                if status.success() {
                    // Parse JSON output from yardbird
                    match serde_json::from_str::<ProofLoopResult>(stdout.trim()) {
                        Ok(result) => {
                            if result.found_proof {
                                return BenchmarkResult::_FoundProof(result);
                            } else {
                                return BenchmarkResult::Success(result);
                            }
                        }
                        Err(e) => {
                            return BenchmarkResult::Error(format!(
                                "Failed to parse JSON from yardbird: {e}\nOutput: {stdout}\nStderr: {stderr}"
                            ));
                        }
                    }
                } else {
                    // Parse common yardbird errors
                    if stderr.contains("No progress") {
                        return BenchmarkResult::NoProgress(ProofLoopResult::default());
                    } else if stderr.contains("counter-example") {
                        return BenchmarkResult::Error("Found counter-example".to_string());
                    } else {
                        return BenchmarkResult::Error(format!(
                            "Process exited with error: {stderr}"
                        ));
                    }
                }
            }
            Ok(None) => {
                // Process still running, check timeout
                if start.elapsed() > timeout {
                    eprintln!("Timeout reached for PID {pid}, killing process");
                    let _ = child.kill();
                    let _ = child.wait();
                    let _ = collect_reader(&mut stdout_reader);
                    let _ = collect_reader(&mut stderr_reader);
                    return BenchmarkResult::Timeout(timeout.as_millis());
                }
                // Sleep briefly before checking again
                thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                return BenchmarkResult::Error(format!("Failed to wait on subprocess: {e}"));
            }
        }
    }
}

fn run_single(
    options: YardbirdOptions,
    retry: usize,
    timeout: u64,
) -> anyhow::Result<StrategyResult> {
    options.validate_ranker_options()?;

    let mut status_code = None;
    let mut run_time = Duration::default();
    // Captures are immutable, so a captured run cannot reuse its output on retry.
    let retry = if matches!(options.strategy, yardbird::Strategy::Concrete)
        || options.solver_capture_dir.is_some()
    {
        1
    } else {
        retry
    };

    for _ in 0..retry {
        let now = Instant::now();
        let filename = options
            .filename
            .as_deref()
            .expect("run_single requires a filename")
            .to_string();

        // Run yardbird in subprocess with timeout
        status_code = Some(run_yardbird_subprocess(
            &options,
            Duration::from_secs(timeout),
        ));

        run_time = now.elapsed();
        // TODO: this is really a hack to try and mitigate z3 model randomness
        if let Some(BenchmarkResult::Timeout(_)) = status_code {
            println!("  retrying: {filename}");
            continue;
        } else if let Some(BenchmarkResult::Error(_)) = status_code {
            println!("  retrying error: {filename}");
            continue;
        } else if let Some(BenchmarkResult::NoProgress(_)) = status_code {
            println!("  retrying no progress: {filename}");
            continue;
        } else {
            break;
        }
    }

    match status_code {
        Some(result) => Ok(StrategyResult {
            solver: options.solver,
            strategy: options.strategy,
            result,
            cost_function: options.cost_function,
            egraph_builder: options.egraph_builder,
            run_time: run_time.as_millis(),
            depth: options.depth,
            record_decisions: options.record_decisions || options.train,
            solver_capture_dir: options.solver_capture_dir,
        }),
        None => Err(anyhow!("Failed to run")),
    }
}

fn get_git_commit() -> Option<String> {
    std::process::Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .and_then(|output| {
            if output.status.success() {
                String::from_utf8(output.stdout)
                    .ok()
                    .map(|s| s.trim().to_string())
            } else {
                None
            }
        })
}

fn run_legacy_mode(options: GardenOptions) -> anyhow::Result<()> {
    if options.solver_capture_root.is_some() {
        return Err(anyhow!(
            "--solver-capture-root requires --config so capture paths can be assigned to matrix results"
        ));
    }
    let examples = options
        .clone()
        .examples
        .unwrap_or_else(|| PathBuf::from("examples"));
    let depth = options.depth.unwrap_or(10);
    let timeout = options.timeout.unwrap_or(30);
    let retry = options.retry.unwrap_or(2);
    let cost_function = options
        .cost_function
        .unwrap_or(yardbird::CostFunction::BmcCost);
    let training_run_version = effective_training_run_version(&options);

    let include: Vec<_> = options
        .include
        .iter()
        .map(|skip| Pattern::new(skip))
        .collect::<Result<_, _>>()?;

    let exclude: Vec<_> = options
        .skip
        .iter()
        .map(|skip| Pattern::new(skip))
        .collect::<Result<_, _>>()?;

    let benchmarks = discover_benchmarks(
        &examples,
        &include,
        &exclude,
        options.limit,
        options.sample_seed.unwrap_or(0),
        options.require_array_reads_and_writes,
    )?;

    let results: Vec<_> = benchmarks
        .iter()
        .enumerate()
        .map(|(idx, filename)| {
            println!("[{}/{}] {filename}", idx + 1, benchmarks.len());
            Ok(Benchmark {
                example: filename.clone(),
                result: options
                    .strategy
                    .iter()
                    .map(|strat| {
                        println!("  using strat: {strat:?}");
                        run_single(
                            YardbirdOptions {
                                command: None,
                                filename: Some(filename.clone()),
                                depth,
                                print_file: false,
                                interpolate: false,
                                repl: false,
                                strategy: *strat,
                                run_ic3ia: options.run_ic3ia,
                                cost_function,
                                egraph_builder: options.egraph_builder,
                                solver: options.solver,
                                theory: yardbird::Theory::Array,
                                json_output: false,
                                dump_solver: None,
                                track_instantiations: options.track_instantiations,
                                dump_unsat_core: None,
                                instantiation_strategy:
                                    yardbird::InstantiationStrategyType::FullUnroll,
                                train: options.train,
                                train_reset: false,
                                database_url: options.database_url.clone(),
                                training_run_version: training_run_version.clone(),
                                verbose: false,
                                profile: options.profile,
                                solver_capture_dir: None,
                                record_decisions: options.record_decisions,
                                synthesis_trigger: options.synthesis_trigger,
                                synthesis_guard_policy: options.synthesis_guard_policy,
                                synthesis_after: options.synthesis_after,
                                synthesis_refinement_limit_window: options
                                    .synthesis_refinement_limit_window,
                                synthesis_repeated_pattern_threshold: options
                                    .synthesis_repeated_pattern_threshold,
                                ranker_model: options.ranker_model.clone(),
                            },
                            retry,
                            timeout,
                        )
                    })
                    .collect::<anyhow::Result<_>>()?,
            })
        })
        .collect::<anyhow::Result<_>>()?;

    let suite = BenchmarkSuite {
        metadata: SuiteMetadata {
            timestamp: Utc::now(),
            git_commit: get_git_commit(),
            config_name: None,
            total_benchmarks: results.len(),
            yardbird_version: env!("CARGO_PKG_VERSION").to_string(),
        },
        benchmarks: results,
    };

    if let Some(output) = options.output {
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(output)?;
        if options.pretty {
            serde_json::to_writer_pretty(file, &suite)?;
        } else {
            serde_json::to_writer(file, &suite)?;
        }
    } else {
        println!("{}", serde_json::to_string_pretty(&suite)?);
    }

    Ok(())
}

fn run_config_based(options: GardenOptions, config: BenchmarkConfig) -> anyhow::Result<()> {
    let runs = config.generate_benchmark_runs(options.matrix.as_deref())?;
    let training_run_version = effective_training_run_version(&options);

    println!("Running {} benchmark configurations", runs.len());

    let examples_dir = options
        .examples
        .clone()
        .unwrap_or(config.global.examples_dir.clone());

    let include: Vec<_> = if options.include.is_empty() {
        config.global.include_patterns.clone()
    } else {
        options.include.clone()
    }
    .iter()
    .map(|pattern| Pattern::new(pattern))
    .collect::<Result<_, _>>()?;

    let exclude: Vec<_> = if options.skip.is_empty() {
        config.global.exclude_patterns.clone()
    } else {
        options.skip.clone()
    }
    .iter()
    .map(|pattern| Pattern::new(pattern))
    .collect::<Result<_, _>>()?;

    let benchmark_limit = options.limit.or(config.global.benchmark_limit);
    let sample_seed = options.sample_seed.unwrap_or(config.global.sample_seed);
    let jobs = options.jobs.unwrap_or(config.global.jobs);
    let retry_count = config.global.retry_count;
    let require_array_reads_and_writes =
        options.require_array_reads_and_writes || config.global.require_array_reads_and_writes;
    anyhow::ensure!(jobs > 0, "--jobs must be greater than zero");

    let benchmarks = discover_benchmarks(
        &examples_dir,
        &include,
        &exclude,
        benchmark_limit,
        sample_seed,
        require_array_reads_and_writes,
    )?;

    println!(
        "Selected {} VMT benchmarks from {}{}{} (sample seed: {sample_seed}, jobs: {jobs})",
        benchmarks.len(),
        examples_dir.display(),
        benchmark_limit
            .map(|limit| format!(", limit: {limit}"))
            .unwrap_or_default(),
        if require_array_reads_and_writes {
            ", requiring array reads+writes"
        } else {
            ""
        },
    );

    let mut all_benchmarks = Vec::new();

    for (run_idx, run) in runs.iter().enumerate() {
        println!(
            "[Config {}/{}] Running: {}",
            run_idx + 1,
            runs.len(),
            run.name
        );

        let next_index = Arc::new(AtomicUsize::new(0));
        let (result_sender, result_receiver) = mpsc::channel();
        let worker_count = jobs.min(benchmarks.len()).max(1);
        let mut ordered_results = (0..benchmarks.len())
            .map(|_| None)
            .collect::<Vec<Option<anyhow::Result<Benchmark>>>>();

        thread::scope(|scope| {
            for _ in 0..worker_count {
                let next_index = Arc::clone(&next_index);
                let result_sender = result_sender.clone();
                let benchmarks = &benchmarks;
                let options = &options;
                let training_run_version = &training_run_version;
                let run = run.clone();

                scope.spawn(move || loop {
                    let idx = next_index.fetch_add(1, Ordering::Relaxed);
                    let Some(filename) = benchmarks.get(idx) else {
                        break;
                    };
                    println!("  [{}/{}] {filename}", idx + 1, benchmarks.len());
                    let result = run_config_benchmark(
                        filename,
                        run_idx,
                        idx,
                        &run,
                        options,
                        training_run_version,
                        retry_count,
                    );
                    if result_sender.send((idx, result)).is_err() {
                        break;
                    }
                });
            }
            drop(result_sender);

            for (idx, result) in result_receiver {
                ordered_results[idx] = Some(result);
            }
        });

        let results = ordered_results
            .into_iter()
            .map(|result| result.expect("every benchmark worker must return a result"))
            .collect::<anyhow::Result<Vec<_>>>()?;

        all_benchmarks.extend(results);
    }

    let suite = BenchmarkSuite {
        metadata: SuiteMetadata {
            timestamp: Utc::now(),
            git_commit: get_git_commit(),
            config_name: options.matrix.clone(),
            total_benchmarks: all_benchmarks.len(),
            yardbird_version: env!("CARGO_PKG_VERSION").to_string(),
        },
        benchmarks: all_benchmarks,
    };

    if let Some(output) = options.output {
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(output)?;
        if options.pretty || config.output.pretty_json {
            serde_json::to_writer_pretty(file, &suite)?;
        } else {
            serde_json::to_writer(file, &suite)?;
        }
    } else {
        println!("{}", serde_json::to_string_pretty(&suite)?);
    }

    Ok(())
}

fn run_config_benchmark(
    filename: &str,
    run_idx: usize,
    benchmark_idx: usize,
    run: &config::BenchmarkRun,
    options: &GardenOptions,
    training_run_version: &Option<String>,
    retry_count: usize,
) -> anyhow::Result<Benchmark> {
    let solver_capture_dir = options.solver_capture_root.as_ref().map(|root| {
        root.join(format!("{run_idx:04}"))
            .join(format!("{benchmark_idx:04}"))
    });
    let result = run_single(
        YardbirdOptions {
            command: None,
            filename: Some(filename.to_string()),
            depth: run.depth,
            print_file: false,
            interpolate: false,
            repl: false,
            strategy: run.strategy,
            run_ic3ia: options.run_ic3ia,
            cost_function: run.cost_function,
            egraph_builder: run.egraph_builder,
            solver: run.solver,
            theory: yardbird::Theory::Array,
            json_output: false,
            dump_solver: None,
            track_instantiations: options.track_instantiations,
            dump_unsat_core: None,
            instantiation_strategy: yardbird::InstantiationStrategyType::FullUnroll,
            train: options.train,
            train_reset: false,
            database_url: options.database_url.clone(),
            training_run_version: training_run_version.clone(),
            verbose: false,
            profile: options.profile,
            solver_capture_dir,
            record_decisions: options.record_decisions,
            synthesis_trigger: options.synthesis_trigger,
            synthesis_guard_policy: options.synthesis_guard_policy,
            synthesis_after: options.synthesis_after,
            synthesis_refinement_limit_window: options.synthesis_refinement_limit_window,
            synthesis_repeated_pattern_threshold: options.synthesis_repeated_pattern_threshold,
            ranker_model: options.ranker_model.clone(),
        },
        retry_count,
        run.timeout_seconds,
    )?;
    Ok(Benchmark {
        example: filename.to_string(),
        result: vec![result],
    })
}

fn discover_benchmarks(
    root: &Path,
    include: &[Pattern],
    exclude: &[Pattern],
    limit: Option<usize>,
    sample_seed: u64,
    require_array_reads_and_writes: bool,
) -> anyhow::Result<Vec<String>> {
    let mut paths = Vec::new();
    let mut visited_directories = HashSet::new();
    collect_vmt_files(root, &mut visited_directories, &mut paths)?;
    paths.retain(|path| {
        (include.is_empty() || include.iter().any(|pattern| pattern.matches_path(path)))
            && !exclude.iter().any(|pattern| pattern.matches_path(path))
    });
    if require_array_reads_and_writes {
        paths.retain(|path| match benchmark_has_array_reads_and_writes(path) {
            Ok(eligible) => eligible,
            Err(error) => {
                eprintln!(
                    "Skipping {} while checking array activity: {error:#}",
                    path.display()
                );
                false
            }
        });
    }
    paths.sort();

    if let Some(limit) = limit {
        paths.sort_by(|left, right| {
            stable_sample_rank(left, sample_seed)
                .cmp(&stable_sample_rank(right, sample_seed))
                .then_with(|| left.cmp(right))
        });
        paths.truncate(limit);
        paths.sort();
    }

    Ok(paths
        .into_iter()
        .map(|path| path.to_string_lossy().into_owned())
        .collect())
}

fn benchmark_has_array_reads_and_writes(path: &Path) -> anyhow::Result<bool> {
    let contents = fs::read_to_string(path)?;
    let (has_read, has_write) = array_operation_presence(&contents);
    Ok(has_read && has_write)
}

fn array_operation_presence(contents: &str) -> (bool, bool) {
    // Scan iteratively so deeply nested external terms cannot overflow Garden's stack.
    let bytes = contents.as_bytes();
    let mut has_read = false;
    let mut has_write = false;
    let mut index = 0;

    while index < bytes.len() && !(has_read && has_write) {
        match bytes[index] {
            b';' => {
                index += 1;
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
            }
            b'"' => {
                index += 1;
                while index < bytes.len() {
                    if bytes[index] == b'"' {
                        if index + 1 < bytes.len() && bytes[index + 1] == b'"' {
                            index += 2;
                            continue;
                        }
                        index += 1;
                        break;
                    }
                    index += 1;
                }
            }
            b'|' => {
                index += 1;
                while index < bytes.len() && bytes[index] != b'|' {
                    index += 1;
                }
                index = (index + 1).min(bytes.len());
            }
            b'(' => {
                index += 1;
                while index < bytes.len() && bytes[index].is_ascii_whitespace() {
                    index += 1;
                }
                let symbol_start = index;
                while index < bytes.len()
                    && !bytes[index].is_ascii_whitespace()
                    && !matches!(bytes[index], b'(' | b')' | b';')
                {
                    index += 1;
                }
                match &bytes[symbol_start..index] {
                    b"select" => has_read = true,
                    b"store" => has_write = true,
                    _ => {}
                }
            }
            _ => index += 1,
        }
    }

    (has_read, has_write)
}

fn collect_vmt_files(
    path: &Path,
    visited_directories: &mut HashSet<PathBuf>,
    files: &mut Vec<PathBuf>,
) -> anyhow::Result<()> {
    let metadata = fs::metadata(path)?;
    if metadata.is_file() {
        if path
            .extension()
            .and_then(|extension| extension.to_str())
            .is_some_and(|extension| extension.eq_ignore_ascii_case("vmt"))
        {
            files.push(path.to_path_buf());
        }
        return Ok(());
    }
    if !metadata.is_dir() {
        return Ok(());
    }

    let canonical = fs::canonicalize(path)?;
    if !visited_directories.insert(canonical) {
        return Ok(());
    }
    for entry in fs::read_dir(path)? {
        collect_vmt_files(&entry?.path(), visited_directories, files)?;
    }
    Ok(())
}

fn stable_sample_rank(path: &Path, sample_seed: u64) -> u64 {
    const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x100000001b3;
    let mut hash = FNV_OFFSET_BASIS;
    for byte in sample_seed
        .to_le_bytes()
        .into_iter()
        .chain(path.to_string_lossy().bytes())
    {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

fn main() -> anyhow::Result<()> {
    let options = GardenOptions::parse();

    if let Some(config_path) = &options.config {
        let config = BenchmarkConfig::from_file(config_path)?;
        run_config_based(options, config)
    } else {
        run_legacy_mode(options)
    }
}

#[cfg(test)]
mod tests {
    use super::{array_operation_presence, discover_benchmarks, Pattern};
    use std::fs;

    #[test]
    fn benchmark_discovery_is_recursive_sorted_and_vmt_only() {
        let root = tempfile::tempdir().expect("temporary corpus");
        fs::create_dir_all(root.path().join("family/nested")).expect("nested corpus");
        fs::write(root.path().join("z.vmt"), "").expect("top-level VMT");
        fs::write(root.path().join("family/a.VMT"), "").expect("uppercase VMT");
        fs::write(root.path().join("family/nested/b.vmt"), "").expect("nested VMT");
        fs::write(root.path().join("family/ignore.smt2"), "").expect("non-VMT input");

        let benchmarks = discover_benchmarks(root.path(), &[], &[], None, 0, false)
            .expect("benchmark discovery should succeed");
        let relative = benchmarks
            .iter()
            .map(|path| {
                std::path::Path::new(path)
                    .strip_prefix(root.path())
                    .expect("path should stay below the corpus")
                    .to_string_lossy()
                    .into_owned()
            })
            .collect::<Vec<_>>();

        assert_eq!(relative, ["family/a.VMT", "family/nested/b.vmt", "z.vmt"]);
    }

    #[test]
    fn benchmark_sampling_is_bounded_reproducible_and_filterable() {
        let root = tempfile::tempdir().expect("temporary corpus");
        for index in 0..40 {
            let family = if index % 2 == 0 { "keep" } else { "skip" };
            fs::create_dir_all(root.path().join(family)).expect("family directory");
            fs::write(root.path().join(format!("{family}/{index:02}.vmt")), "")
                .expect("sample VMT");
        }
        let include = [Pattern::new("**/keep/*.vmt").expect("valid include glob")];

        let first = discover_benchmarks(root.path(), &include, &[], Some(7), 42, false)
            .expect("first sample");
        let repeated = discover_benchmarks(root.path(), &include, &[], Some(7), 42, false)
            .expect("repeated sample");
        let different_seed = discover_benchmarks(root.path(), &include, &[], Some(7), 43, false)
            .expect("alternate sample");

        assert_eq!(first.len(), 7);
        assert_eq!(first, repeated);
        assert_ne!(first, different_seed);
        assert!(first.iter().all(|path| path.contains("/keep/")));
    }

    #[test]
    fn array_activity_filter_runs_before_sampling() {
        let root = tempfile::tempdir().expect("temporary corpus");
        let array_example = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../examples/array/array_copy.vmt");
        fs::copy(array_example, root.path().join("array.vmt")).expect("array benchmark fixture");
        fs::write(
            root.path().join("scalar.vmt"),
            r#"
(declare-fun x () Int)
(declare-fun x_next () Int)
(define-fun .x () Int (! x :next x_next))
(define-fun init () Bool (! (= x 0) :init true))
(define-fun trans () Bool (! (= x_next (+ x 1)) :trans true))
(define-fun property () Bool (! (>= x 0) :invar-property 0))
"#,
        )
        .expect("scalar benchmark fixture");

        let benchmarks = discover_benchmarks(root.path(), &[], &[], Some(10), 7, true)
            .expect("array activity filtering should succeed");

        assert_eq!(benchmarks.len(), 1);
        assert!(benchmarks[0].ends_with("array.vmt"));
    }

    #[test]
    fn array_activity_scan_ignores_comments_and_strings() {
        assert_eq!(
            array_operation_presence("; (select a i)\n(echo \"(store a i v)\")"),
            (false, false)
        );
        assert_eq!(
            array_operation_presence("(and (= (select a i) 0) (= (store a i 1) next))"),
            (true, true)
        );
    }
}
