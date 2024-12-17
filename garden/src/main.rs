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
    time::Duration,
};
use yardbird::{proof_loop, ProofLoopResult, YardbirdOptions};

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
}

#[derive(Debug, Serialize)]
struct SerializableProofResult {
    pub used_instances: Vec<String>,
    pub const_instances: Vec<String>,
}

impl From<ProofLoopResult> for SerializableProofResult {
    fn from(value: ProofLoopResult) -> Self {
        SerializableProofResult {
            used_instances: value.used_instances,
            const_instances: value.const_instances,
        }
    }
}

#[derive(Debug, Serialize)]
enum BenchmarkResult {
    Success(SerializableProofResult),
    Timeout(u128),
    Error(String),
    Panic(String),
}

#[derive(Debug, Serialize)]
struct Benchmark {
    example: String,
    result: BenchmarkResult,
}

enum TimeoutFnResult<T> {
    Ok(T),
    Panic(String),
}

fn run_with_timeout<F, T, E>(f: F, timeout: Duration) -> BenchmarkResult
where
    F: FnOnce() -> Result<T, E> + Send + std::panic::UnwindSafe + 'static,
    T: Send + std::fmt::Debug + Into<SerializableProofResult> + 'static,
    E: Send + std::fmt::Display + 'static,
{
    let (tx, rx) = mpsc::channel::<TimeoutFnResult<Result<T, E>>>();
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
            Err(err) => BenchmarkResult::Error(format!("{err}")),
        },
        Ok(TimeoutFnResult::Panic(msg)) => BenchmarkResult::Panic(msg),
        Err(RecvTimeoutError::Timeout) => BenchmarkResult::Timeout(timeout.as_millis()),
        Err(RecvTimeoutError::Disconnected) => unreachable!(),
    }
}

fn run_single(options: YardbirdOptions) -> anyhow::Result<Benchmark> {
    println!("running: {}", options.filename);
    let mut status_code = None;
    for i in 0..5 {
        let proof_options = options.clone();
        status_code = Some(run_with_timeout(
            move || proof_loop(&proof_options),
            Duration::from_secs(10 + (i * 5)),
        ));
        // TODO: this is really a hack to try and get around z3 model randomness
        if let Some(BenchmarkResult::Timeout(_)) = status_code {
            println!("  retrying: {}", options.filename);
            continue;
        } else if let Some(BenchmarkResult::Error(_)) = status_code {
            println!("  retrying error: {}", options.filename);
            continue;
        } else {
            break;
        }
    }

    match status_code {
        Some(result) => Ok(Benchmark {
            example: options.filename,
            result,
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

    let results: Vec<_> = read_dir(options.base)?
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
        .map(|filename| {
            let yardbird_options = YardbirdOptions {
                filename,
                depth: options.depth,
                bmc_count: 10,
                print_vmt: false,
                interpolate: false,
            };
            run_single(yardbird_options)
        })
        .collect::<Result<_, _>>()?;

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
