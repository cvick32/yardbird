use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::Duration;
use std::{panic, thread};

use smt2parser::vmt::VMTModel;
use yardbird::{Driver, ProofLoopResult, YardbirdOptions};

use crate::ToVMTArgs;

#[derive(Debug)]
enum MacroResult {
    Success(ProofResult),
    Timeout(u128),
    Error(String),
    Panic(String),
}

enum TimeoutFnResult<T> {
    Ok(T),
    Panic(String),
}

#[derive(Debug)]
struct ProofResult {
    pub used_instances: Vec<String>,
    pub _const_instances: Vec<String>,
}

impl From<ProofLoopResult> for ProofResult {
    fn from(value: ProofLoopResult) -> Self {
        ProofResult {
            used_instances: value.used_instances,
            _const_instances: value.const_instances,
        }
    }
}

pub fn run_yardbird(macro_args: ToVMTArgs, vmt: VMTModel) {
    let standard_options = YardbirdOptions::default();
    // Run yardbird proof.
    let status_code = Some(run_with_timeout(
        move || {
            let driver = Driver::new(&standard_options, &z3::Config::new(), vmt);
            driver.check_to_depth(standard_options.depth, 10)
        },
        macro_args.get_timeout(),
    ));

    match status_code {
        Some(result) => match result {
            MacroResult::Success(proof_result) => {
                println!("Yardbird: {:#?}", proof_result.used_instances);
            }
            MacroResult::Timeout(time) => {
                println!("Yardbird timed out after: {time}");
            }
            MacroResult::Error(err) => {
                println!("Yardbird error: {}", err);
            }
            MacroResult::Panic(p) => {
                println!("Yardbird panic: {}", p);
            }
        },
        None => todo!(),
    }
}

fn run_with_timeout<F, T, E>(f: F, timeout: Duration) -> MacroResult
where
    F: FnOnce() -> Result<T, E> + Send + std::panic::UnwindSafe + 'static,
    T: Send + std::fmt::Debug + Into<ProofResult> + 'static,
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
            Ok(proof_result) => MacroResult::Success(proof_result.into()),
            Err(err) => MacroResult::Error(format!("{err}")),
        },
        Ok(TimeoutFnResult::Panic(msg)) => MacroResult::Panic(msg),
        Err(RecvTimeoutError::Timeout) => MacroResult::Timeout(timeout.as_millis()),
        Err(RecvTimeoutError::Disconnected) => unreachable!(),
    }
}
