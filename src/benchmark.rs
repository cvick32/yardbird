use std::{
    fs::{read_dir, File},
    io::Write,
    sync::mpsc::{self, RecvTimeoutError},
    thread,
    time::Duration,
};

use log::info;
use serde::Serialize;

use crate::{model_from_options, proof_loop, YardbirdOptions};

#[derive(Debug, Serialize)]
enum BenchResult {
    Good,
    Timeout,
    Panic,
}

fn run_with_timeout<F, T>(f: F, timeout: Duration) -> BenchResult
where
    F: FnOnce() -> Option<T> + Send + 'static,
    T: Send + 'static,
{
    let (tx, rx) = mpsc::channel();
    let _ = thread::spawn(move || {
        let result = f();
        if let Ok(()) = tx.send(result) {}
    });

    match rx.recv_timeout(timeout) {
        Ok(_) => BenchResult::Good,
        Err(RecvTimeoutError::Timeout) => BenchResult::Timeout,
        Err(RecvTimeoutError::Disconnected) => BenchResult::Panic,
    }
}

#[derive(Debug, Serialize)]
struct BenchmarkResult {
    example_name: String,
    result: BenchResult,
}

pub fn run_benchmarks(options: &YardbirdOptions) -> anyhow::Result<()> {
    let mut bench_results = vec![];
    for path in read_dir("./examples/")? {
        let path_string: String = path?.path().to_string_lossy().to_string();
        if path_string.contains("2dim") {
            info!("Skipping: {}", path_string);
            continue;
        }
        info!("Trying: {}", path_string);
        let new_options = YardbirdOptions {
            filename: path_string.clone(),
            ..options.clone()
        };
        let abstract_vmt_model = model_from_options(&new_options);
        let result = run_with_timeout(
            move || proof_loop(&new_options, abstract_vmt_model).ok(),
            Duration::from_secs(10),
        );
        bench_results.push(BenchmarkResult {
            example_name: path_string.clone(),
            result,
        });
    }
    info!("{:?}", bench_results);
    let mut output = File::create("benchmark-results.json")?;
    let _ = output.write(serde_json::to_string(&bench_results)?.as_bytes());
    info!("Tried {} benchmarks.", bench_results.len());
    Ok(())
}
