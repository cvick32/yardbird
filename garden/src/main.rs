use anyhow::anyhow;
use chrono::{DateTime, Utc};
use clap::Parser;
use glob::Pattern;
use serde::Serialize;
use std::{
    fs::{read_dir, OpenOptions},
    path::PathBuf,
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};
use yardbird::{ProofLoopResult, YardbirdOptions};

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

    #[arg(short, long)]
    pub cost_function: Option<yardbird::CostFunction>,
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
    strategy: yardbird::Strategy,
    cost_function: yardbird::CostFunction,
    result: BenchmarkResult,
    run_time: u128,
    depth: u16,
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

    // Build command line arguments for yardbird with JSON output
    let mut child = Command::new(&yardbird_bin)
        .arg("--filename")
        .arg(&options.filename)
        .arg("--depth")
        .arg(options.depth.to_string())
        .arg("--strategy")
        .arg(options.strategy.to_string())
        .arg("--cost-function")
        .arg(options.cost_function.to_string())
        .arg("--json-output")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn yardbird subprocess");

    let pid = child.id();
    let start = Instant::now();

    // Poll the subprocess until it completes or times out
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                // Process completed, read stdout for JSON
                let mut stdout = String::new();
                if let Some(mut pipe) = child.stdout.take() {
                    use std::io::Read;
                    let _ = pipe.read_to_string(&mut stdout);
                }

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
                                "Failed to parse JSON from yardbird: {e}\nOutput: {stdout}"
                            ));
                        }
                    }
                } else {
                    // Check stderr for error messages
                    let mut stderr = String::new();
                    if let Some(mut pipe) = child.stderr.take() {
                        use std::io::Read;
                        let _ = pipe.read_to_string(&mut stderr);
                    }

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
    let mut status_code = None;
    let mut run_time = Duration::default();
    // don't retry for the concrete strategy
    let retry = if matches!(options.strategy, yardbird::Strategy::Concrete) {
        1
    } else {
        retry
    };

    for _ in 0..retry {
        let now = Instant::now();
        let filename = options.filename.to_string();

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
            strategy: options.strategy,
            result,
            cost_function: options.cost_function,
            run_time: run_time.as_millis(),
            depth: options.depth,
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
    let examples = options
        .examples
        .unwrap_or_else(|| PathBuf::from("examples"));
    let depth = options.depth.unwrap_or(10);
    let timeout = options.timeout.unwrap_or(30);
    let retry = options.retry.unwrap_or(2);
    let cost_function = options
        .cost_function
        .unwrap_or(yardbird::CostFunction::BmcCost);

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

    let benchmarks: Vec<_> = read_dir(examples)?
        .filter_map(|path| path.ok())
        .flat_map(|path| {
            if path.path().is_dir() {
                read_dir(path.path())
                    .unwrap()
                    .filter_map(|path| path.ok())
                    .collect()
            } else {
                vec![path]
            }
        })
        .filter(|entry| {
            include.is_empty() || include.iter().any(|glob| glob.matches_path(&entry.path()))
        })
        .filter(|entry| !exclude.iter().any(|glob| glob.matches_path(&entry.path())))
        .map(|entry| entry.path().to_string_lossy().to_string())
        .collect();

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
                                filename: filename.clone(),
                                depth,
                                print_vmt: false,
                                interpolate: false,
                                repl: false,
                                strategy: *strat,
                                run_ic3ia: options.run_ic3ia,
                                cost_function,
                                theory: yardbird::Theory::Array,
                                json_output: false,
                                dump_solver: None,
                                track_instantiations: false,
                                dump_unsat_core: None,
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

    println!("Running {} benchmark configurations", runs.len());

    let examples_dir = options
        .examples
        .unwrap_or(config.global.examples_dir.clone());

    let include: Vec<_> = if options.include.is_empty() {
        config.global.include_patterns
    } else {
        options.include
    }
    .iter()
    .map(|pattern| Pattern::new(pattern))
    .collect::<Result<_, _>>()?;

    let exclude: Vec<_> = if options.skip.is_empty() {
        config.global.exclude_patterns
    } else {
        options.skip
    }
    .iter()
    .map(|pattern| Pattern::new(pattern))
    .collect::<Result<_, _>>()?;

    let benchmarks: Vec<_> = read_dir(&examples_dir)?
        .filter_map(|path| path.ok())
        .flat_map(|path| {
            if path.path().is_dir() {
                read_dir(path.path())
                    .unwrap()
                    .filter_map(|path| path.ok())
                    .collect()
            } else {
                vec![path]
            }
        })
        .filter(|entry| {
            include.is_empty() || include.iter().any(|glob| glob.matches_path(&entry.path()))
        })
        .filter(|entry| !exclude.iter().any(|glob| glob.matches_path(&entry.path())))
        .map(|entry| entry.path().to_string_lossy().to_string())
        .collect();

    let mut all_benchmarks = Vec::new();

    for (run_idx, run) in runs.iter().enumerate() {
        println!(
            "[Config {}/{}] Running: {}",
            run_idx + 1,
            runs.len(),
            run.name
        );

        let results: Vec<_> = benchmarks
            .iter()
            .enumerate()
            .map(|(idx, filename)| {
                println!("  [{}/{}] {filename}", idx + 1, benchmarks.len());
                let result = run_single(
                    YardbirdOptions {
                        filename: filename.clone(),
                        depth: run.depth,
                        print_vmt: false,
                        interpolate: false,
                        repl: false,
                        strategy: run.strategy,
                        run_ic3ia: options.run_ic3ia,
                        cost_function: run.cost_function,
                        theory: yardbird::Theory::Array,
                        json_output: false,
                        dump_solver: None,
                        track_instantiations: false,
                        dump_unsat_core: None,
                    },
                    config.global.retry_count,
                    run.timeout_seconds,
                )?;
                Ok(Benchmark {
                    example: format!("{}_{}", run.name, filename),
                    result: vec![result],
                })
            })
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

fn main() -> anyhow::Result<()> {
    let options = GardenOptions::parse();

    if let Some(config_path) = &options.config {
        let config = BenchmarkConfig::from_file(config_path)?;
        run_config_based(options, config)
    } else {
        run_legacy_mode(options)
    }
}
