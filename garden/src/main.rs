use anyhow::anyhow;
use clap::Parser;
use glob::Pattern;
use serde::Serialize;
use std::{
    fs::{read_dir, OpenOptions},
    panic,
    path::PathBuf,
    sync::mpsc::{self, RecvTimeoutError},
    thread,
    time::{Duration, Instant},
};
use yardbird::{model_from_options, Driver, ProofLoopResult, YardbirdOptions};

#[derive(Parser, Debug, Clone)]
#[command(version, about, long_about = None)]
struct Options {
    /// Directory to find vmt files in.
    pub base: PathBuf,

    /// BMC depth until quitting.
    #[arg(short, long, default_value_t = 10)]
    pub depth: u8,

    /// Timeout for each benchmark
    #[arg(short, long, default_value_t = 30)]
    pub timeout: usize,

    /// Benchmarks to include.
    #[arg(short, long)]
    pub include: Vec<String>,

    /// Benchmarks to skip.
    #[arg(short, long)]
    pub skip: Vec<String>,

    /// Optionally a file to output results to.
    #[arg(short, long)]
    pub output: Option<PathBuf>,

    /// Should we write out pretty json?
    #[arg(short, long)]
    pub pretty: bool,

    /// Strategy to run benchmarks with
    #[arg(long)]
    pub strategy: Vec<yardbird::Strategy>,

    #[arg(long, default_value_t = 2)]
    pub retry: usize,
}

#[derive(Debug, Serialize)]
struct SerializableProofResult {
    pub used_instances: Vec<String>,
    pub const_instances: Vec<String>,
}

impl From<ProofLoopResult> for SerializableProofResult {
    fn from(value: ProofLoopResult) -> Self {
        SerializableProofResult {
            used_instances: value
                .used_instances
                .iter()
                .map(ToString::to_string)
                .collect(),
            const_instances: value
                .const_instances
                .iter()
                .map(ToString::to_string)
                .collect(),
        }
    }
}

#[derive(Debug, Serialize)]
enum BenchmarkResult {
    Success(SerializableProofResult),
    NoProgress(SerializableProofResult),
    Timeout(u128),
    Error(String),
    Panic(String),
}

#[derive(Debug, Serialize)]
struct Benchmark {
    example: String,
    result: Vec<StrategyResult>,
}

#[derive(Debug, Serialize)]
struct StrategyResult {
    strategy: yardbird::Strategy,
    result: BenchmarkResult,
    run_time: u128,
    depth: u8,
}

enum TimeoutFnResult {
    Ok(yardbird::Result<ProofLoopResult>),
    Panic(String),
}

fn run_with_timeout<F>(f: F, timeout: Duration) -> BenchmarkResult
where
    F: FnOnce() -> yardbird::Result<ProofLoopResult> + Send + std::panic::UnwindSafe + 'static,
{
    let (tx, rx) = mpsc::channel::<TimeoutFnResult>();
    let _ = thread::spawn(move || {
        // remove the default panic hook that prints the message
        panic::set_hook(Box::new(|_| {}));

        // catch the panic so that we can extract the message
        let result = panic::catch_unwind(f);
        match result {
            Ok(inner) => {
                tx.send(TimeoutFnResult::Ok(inner)).unwrap();
            }
            Err(panic) => {
                let panic_string = match panic.downcast::<String>() {
                    Ok(v) => *v,
                    Err(e) => match e.downcast::<&str>() {
                        Ok(v) => v.to_string(),
                        Err(_) => "Unknown panic error".to_string(),
                    },
                };
                tx.send(TimeoutFnResult::Panic(panic_string)).unwrap();
            }
        }
    });

    match rx.recv_timeout(timeout) {
        Ok(TimeoutFnResult::Ok(res)) => match res {
            Ok(proof_result) => BenchmarkResult::Success(proof_result.into()),
            Err(yardbird::Error::NoProgress { instantiations, .. }) => {
                BenchmarkResult::NoProgress(SerializableProofResult {
                    used_instances: instantiations.iter().map(ToString::to_string).collect(),
                    const_instances: vec![],
                })
            }
            Err(err) => BenchmarkResult::Error(format!("{err}")),
        },
        Ok(TimeoutFnResult::Panic(msg)) => BenchmarkResult::Panic(msg),
        Err(RecvTimeoutError::Timeout) => BenchmarkResult::Timeout(timeout.as_millis()),
        Err(RecvTimeoutError::Disconnected) => unreachable!(),
    }
}

fn run_single(options: YardbirdOptions, retry: usize) -> anyhow::Result<StrategyResult> {
    let mut status_code = None;
    let mut timed_out_count = 0;
    let mut run_time = Duration::default();
    // don't retry for the concrete strategy
    let retry = if matches!(options.strategy, yardbird::Strategy::Concrete) {
        1
    } else {
        retry
    };
    for _ in 0..retry {
        let proof_options = options.clone();
        let abstract_vmt_model = model_from_options(&proof_options);
        let now = Instant::now();
        let filename = options.filename.to_string();
        let options = options.clone();
        status_code = Some(run_with_timeout(
            move || {
                let ctx = z3::Context::new(&z3::Config::new());
                let mut driver = Driver::new(&ctx, abstract_vmt_model);
                let strategy = options.build_strategy();
                driver.check_strategy(proof_options.depth, strategy)
            },
            Duration::from_secs(20 + (timed_out_count * 5)),
        ));
        run_time = now.elapsed();
        // TODO: this is really a hack to try and mitigate z3 model randomness
        if let Some(BenchmarkResult::Timeout(_)) = status_code {
            println!("  retrying: {}", filename);
            timed_out_count += 1;
            continue;
        } else if let Some(BenchmarkResult::Error(_)) = status_code {
            println!("  retrying error: {}", filename);
            continue;
        } else if let Some(BenchmarkResult::NoProgress(_)) = status_code {
            println!("  retrying no progress: {}", filename);
            continue;
        } else {
            break;
        }
    }

    match status_code {
        Some(result) => Ok(StrategyResult {
            strategy: options.strategy,
            result,
            run_time: run_time.as_millis(),
            depth: options.depth,
        }),
        None => Err(anyhow!("Failed to run")),
    }
}

fn main() -> anyhow::Result<()> {
    let options = Options::parse();

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

    let benchmarks: Vec<_> = read_dir(options.base)?
        .filter_map(|path| path.ok())
        // recurse one level
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
        // include all files that match an include pattern
        .filter(|entry| {
            include.is_empty() || include.iter().any(|glob| glob.matches_path(&entry.path()))
        })
        // and exlude all the ones matching a skip pattern
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
                                depth: options.depth,
                                bmc_count: 10,
                                print_vmt: false,
                                interpolate: false,
                                repl: false,
                                strategy: *strat,
                                invoke_ic3ia: false,
                            },
                            options.retry,
                        )
                    })
                    .collect::<anyhow::Result<_>>()?,
            })
        })
        .collect::<anyhow::Result<_>>()?;

    if let Some(output) = options.output {
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(output)?;
        if options.pretty {
            serde_json::to_writer_pretty(file, &results)?;
        } else {
            serde_json::to_writer(file, &results)?;
        }
    } else {
        println!("{}", serde_json::to_string_pretty(&results)?);
    }

    Ok(())
}
