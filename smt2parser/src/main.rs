// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use smt2parser::{
    concrete::SyntaxBuilder,
    get_vmt_from_path,
    renaming::{SymbolNormalizer, SymbolNormalizerConfig, TesterModernizer},
    stats::Smt2Counters,
    vmt::{VMTError, VMTModel},
    CommandStream,
};
use std::{
    any::Any,
    panic::{self, AssertUnwindSafe},
    path::{Path, PathBuf},
};
use structopt::StructOpt;
use strum::IntoEnumIterator;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "smt2bin",
    about = "Demo tool for processing files with smt2parser"
)]
struct Options {
    /// Operation
    #[structopt(subcommand)]
    operation: Operation,
}

#[derive(Debug, StructOpt)]
enum Operation {
    Audit {
        /// File or directory containing VMT benchmarks.
        #[structopt(parse(from_os_str))]
        input: PathBuf,
    },
    Print {
        /// Normalize bound symbols to x0, x1..
        #[structopt(long)]
        normalize_symbols: bool,

        /// When normalizing symbols, indices in the range 0..N will be randomly permuted.
        #[structopt(long, default_value = "0")]
        max_randomized_symbols: usize,

        /// Optional seed for randomization purposes.
        #[structopt(long)]
        symbol_randomization_seed: Option<u64>,

        /// Path to the SMT2 files.
        #[structopt(parse(from_os_str))]
        inputs: Vec<PathBuf>,
    },
    Count {
        /// Optional path to keyword file. One keyword per line.
        #[structopt(long, parse(from_os_str))]
        keywords: Option<PathBuf>,

        /// Optional path to symbol file. One symbol per line.
        #[structopt(long, parse(from_os_str))]
        symbols: Option<PathBuf>,

        /// Path to the SMT2 files.
        #[structopt(parse(from_os_str))]
        inputs: Vec<PathBuf>,
    },
    Vmt {
        /// Path to the VMT file.
        #[structopt(parse(from_os_str))]
        input: PathBuf,
    },
}

#[derive(Default)]
struct AuditSummary {
    files: usize,
    parsed: usize,
    syntax_errors: usize,
    vmt_errors: usize,
    panics: usize,
}

enum AuditOutcome {
    Parsed,
    SyntaxError(String),
    VmtError(String),
    Panic(String),
}

fn collect_vmt_files(path: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if path.is_file() {
        if path
            .extension()
            .and_then(|extension| extension.to_str())
            .is_some_and(|extension| extension.eq_ignore_ascii_case("vmt"))
        {
            files.push(path.to_path_buf());
        }
        return Ok(());
    }

    if !path.is_dir() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("audit input does not exist: {}", path.display()),
        ));
    }

    let mut entries = std::fs::read_dir(path)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|entry| entry.path());
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() || file_type.is_file() {
            collect_vmt_files(&path, files)?;
        }
    }
    Ok(())
}

fn audit_vmt(path: &Path) -> AuditOutcome {
    match panic::catch_unwind(AssertUnwindSafe(|| VMTModel::from_path(path))) {
        Ok(Ok(_)) => AuditOutcome::Parsed,
        Ok(Err(VMTError::VisitorError(error))) => AuditOutcome::SyntaxError(error.to_string()),
        Ok(Err(error)) => AuditOutcome::VmtError(error.to_string()),
        Err(payload) => AuditOutcome::Panic(panic_message(payload.as_ref())),
    }
}

fn panic_message(payload: &(dyn Any + Send)) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_string()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "non-string panic payload".to_string()
    }
}

fn single_line(message: &str) -> String {
    message.replace('\n', "\\n")
}

fn audit(input: &Path) -> std::io::Result<()> {
    let mut files = Vec::new();
    collect_vmt_files(input, &mut files)?;
    files.sort();

    let original_panic_hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));

    let mut summary = AuditSummary::default();
    for path in files {
        summary.files += 1;
        match audit_vmt(&path) {
            AuditOutcome::Parsed => summary.parsed += 1,
            AuditOutcome::SyntaxError(error) => {
                summary.syntax_errors += 1;
                eprintln!("SYNTAX_ERROR\t{}\t{}", path.display(), single_line(&error));
            }
            AuditOutcome::VmtError(error) => {
                summary.vmt_errors += 1;
                eprintln!("VMT_ERROR\t{}\t{}", path.display(), single_line(&error));
            }
            AuditOutcome::Panic(error) => {
                summary.panics += 1;
                eprintln!("PANIC\t{}\t{}", path.display(), single_line(&error));
            }
        }
    }

    panic::set_hook(original_panic_hook);
    println!(
        "files={} parsed={} syntax_errors={} vmt_errors={} panics={}",
        summary.files, summary.parsed, summary.syntax_errors, summary.vmt_errors, summary.panics
    );
    Ok(())
}

fn process_file<T, F>(state: T, file_path: PathBuf, mut f: F) -> std::io::Result<T>
where
    T: smt2parser::visitors::Smt2Visitor,
    F: FnMut(T::Command),
    T::Error: std::fmt::Display,
{
    let file = std::io::BufReader::new(std::fs::File::open(&file_path)?);
    let mut stream = CommandStream::new(file, state, file_path.to_str().map(String::from));
    for result in &mut stream {
        match result {
            Ok(command) => f(command),
            Err(error) => {
                eprintln!("{error}");
                break;
            }
        }
    }
    Ok(stream.into_visitor())
}

fn read_words(path: Option<PathBuf>) -> std::io::Result<Vec<String>> {
    match path {
        None => Ok(Vec::new()),
        Some(path) => {
            use std::io::BufRead;
            let file = std::io::BufReader::new(std::fs::File::open(&path)?);
            file.lines().collect()
        }
    }
}

fn main() -> std::io::Result<()> {
    let options = Options::from_args();
    match options.operation {
        Operation::Audit { input } => audit(&input)?,
        Operation::Vmt { input } => {
            let vmt_model = get_vmt_from_path(&input);
            match vmt_model {
                Ok(vm) => {
                    vm.print_stats();
                    println!("{}", vm.as_vmt_string());
                    let _smt = vm.unroll(10);
                    let (abs, _types) = vm.abstract_array_theory();
                    println!("{}", abs.as_vmt_string());
                    let _abs_smt = abs.unroll(10);
                }
                Err(_) => panic!("Could not parse VMT."),
            }
        }

        Operation::Print {
            normalize_symbols,
            max_randomized_symbols,
            symbol_randomization_seed,
            inputs,
        } => {
            let randomization_space = smt2parser::visitors::SymbolKind::iter()
                .map(|k| (k, max_randomized_symbols))
                .collect();
            let randomization_seed = symbol_randomization_seed.unwrap_or_else(rand::random);
            let config = SymbolNormalizerConfig {
                randomization_space,
                randomization_seed,
            };
            if normalize_symbols {
                let mut normalizer = SymbolNormalizer::new(SyntaxBuilder, config);
                for input in inputs {
                    // 1. Parse input commands while rewriting `is-Foo` into `(_ is Foo)` on the fly with TesterModernizer.
                    process_file(TesterModernizer::new(SyntaxBuilder), input, |command| {
                        // 2. Re-visit the syntax for name resolution and normalization.
                        let command = command.accept(&mut normalizer).unwrap();
                        println!("{command}");
                    })?;
                }
            } else {
                for input in inputs {
                    process_file(SyntaxBuilder, input, |command| println!("{command}"))?;
                }
            }
        }
        Operation::Count {
            keywords,
            symbols,
            inputs,
        } => {
            let keywords = read_words(keywords)?;
            let symbols = read_words(symbols)?;
            let mut state = Smt2Counters::new(keywords, symbols);
            for input in inputs {
                state = process_file(state, input, |_| {})?;
            }
            println!("{state:#?}")
        }
    }
    Ok(())
}
