use std::{
    fs,
    io::{BufWriter, Write},
    path::{Path, PathBuf},
};

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use smt2parser::{
    analysis::{
        import_manifest::ImportedBenchmark,
        quantifier_support::{
            analyze_assertion, array_family_allowlist, AnalysisOptions, FileAnalysis,
            FileAnalysisAccumulator, SummaryAccumulator,
        },
    },
    concrete::Command as SmtCommand,
    get_commands_from_path,
};

#[derive(Parser, Debug)]
#[command(name = "bitwuzla_quantifier_support")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    Import {
        #[arg(
            long,
            default_value = "/Users/cvick-admin/Documents/research/cav2023-bitwuzla-artifact/benchmarks/benchmarks"
        )]
        source_root: PathBuf,
        #[arg(
            long,
            default_value = "/Users/cvick-admin/Documents/research/yardbird/examples/bitwuzla"
        )]
        destination_root: PathBuf,
    },
    Classify {
        #[arg(
            long,
            default_value = "/Users/cvick-admin/Documents/research/yardbird/examples/bitwuzla"
        )]
        benchmark_root: PathBuf,
        #[arg(
            long,
            default_value = "/Users/cvick-admin/Documents/research/yardbird/benchmark_results/bitwuzla_quantifier_support"
        )]
        output_root: PathBuf,
        #[arg(long, default_value_t = 100_000_000)]
        max_bytes: u64,
        #[arg(long, default_value_t = false)]
        include_assertion_text: bool,
    },
    ImportAndClassify {
        #[arg(
            long,
            default_value = "/Users/cvick-admin/Documents/research/cav2023-bitwuzla-artifact/benchmarks/benchmarks"
        )]
        source_root: PathBuf,
        #[arg(
            long,
            default_value = "/Users/cvick-admin/Documents/research/yardbird/examples/bitwuzla"
        )]
        destination_root: PathBuf,
        #[arg(
            long,
            default_value = "/Users/cvick-admin/Documents/research/yardbird/benchmark_results/bitwuzla_quantifier_support"
        )]
        output_root: PathBuf,
        #[arg(long, default_value_t = 100_000_000)]
        max_bytes: u64,
        #[arg(long, default_value_t = false)]
        include_assertion_text: bool,
    },
}

fn main() -> Result<()> {
    std::thread::Builder::new()
        .name("bitwuzla-quantifier-support".to_string())
        .stack_size(256 * 1024 * 1024)
        .spawn(run)?
        .join()
        .map_err(|_| anyhow::anyhow!("bitwuzla_quantifier_support worker thread panicked"))?
}

fn run() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::Import {
            source_root,
            destination_root,
        } => {
            let manifest = import_benchmarks(&source_root, &destination_root)?;
            write_import_manifest(&destination_root, &manifest)?;
        }
        Command::Classify {
            benchmark_root,
            output_root,
            max_bytes,
            include_assertion_text,
        } => {
            classify_benchmarks(
                &benchmark_root,
                &output_root,
                max_bytes,
                include_assertion_text,
            )?;
        }
        Command::ImportAndClassify {
            source_root,
            destination_root,
            output_root,
            max_bytes,
            include_assertion_text,
        } => {
            let manifest = import_benchmarks(&source_root, &destination_root)?;
            write_import_manifest(&destination_root, &manifest)?;
            classify_benchmarks(
                &destination_root,
                &output_root,
                max_bytes,
                include_assertion_text,
            )?;
        }
    }
    Ok(())
}

fn import_benchmarks(
    source_root: &Path,
    destination_root: &Path,
) -> Result<Vec<ImportedBenchmark>> {
    let mut manifest = Vec::new();
    for incrementality in ["incremental", "non-incremental"] {
        let root = source_root.join(incrementality);
        if !root.exists() {
            continue;
        }
        for family in array_family_allowlist() {
            let family_root = root.join(family);
            if !family_root.exists() {
                continue;
            }
            for file in collect_smt2_files(&family_root)? {
                let relative_tail = file
                    .strip_prefix(&family_root)
                    .context("failed to strip family root prefix")?;
                let relative_path = PathBuf::from(incrementality)
                    .join(family)
                    .join(relative_tail);
                let destination_path = destination_root.join(&relative_path);
                if let Some(parent) = destination_path.parent() {
                    fs::create_dir_all(parent)?;
                }
                fs::copy(&file, &destination_path)?;
                manifest.push(ImportedBenchmark {
                    source_path: file,
                    relative_path,
                    destination_path,
                    family: (*family).to_string(),
                    incrementality: incrementality.to_string(),
                });
            }
        }
    }
    Ok(manifest)
}

fn write_import_manifest(destination_root: &Path, manifest: &[ImportedBenchmark]) -> Result<()> {
    let manifest_path = destination_root.join("import_manifest.json");
    if let Some(parent) = manifest_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&manifest_path, serde_json::to_string_pretty(manifest)?)?;
    Ok(())
}

fn classify_benchmarks(
    benchmark_root: &Path,
    output_root: &Path,
    max_bytes: u64,
    include_assertion_text: bool,
) -> Result<()> {
    fs::create_dir_all(output_root)?;
    let mut jsonl = fs::File::create(output_root.join("file_analysis.jsonl"))?;
    let mut summary = SummaryAccumulator::default();
    let options = AnalysisOptions {
        include_assertion_text,
    };

    for file in collect_smt2_files(benchmark_root)? {
        let relative_path = file
            .strip_prefix(benchmark_root)
            .context("failed to compute benchmark-relative path")?
            .to_path_buf();
        let file_len = fs::metadata(&file)?.len();
        if file_len > max_bytes {
            let row = FileAnalysis::parse_error(
                relative_path,
                format!("file exceeds max-bytes limit: {file_len} > {max_bytes}"),
            );
            writeln!(jsonl, "{}", serde_json::to_string(&row)?)?;
            summary.observe(&row);
            continue;
        }
        match get_commands_from_path(&file.to_path_buf()) {
            Ok(commands) => {
                let (file_row, assertions) =
                    process_file(&commands, &relative_path, output_root, options)?;
                writeln!(jsonl, "{}", serde_json::to_string(&file_row)?)?;
                write_assertion_analysis(output_root, &relative_path, &assertions)?;
                summary.observe(&file_row);
            }
            Err(err) => {
                let row = FileAnalysis::parse_error(relative_path, err.to_string());
                writeln!(jsonl, "{}", serde_json::to_string(&row)?)?;
                summary.observe(&row);
            }
        }
    }

    write_summary(output_root, &summary)?;
    Ok(())
}

fn process_file(
    commands: &[SmtCommand],
    relative_path: &Path,
    output_root: &Path,
    options: AnalysisOptions,
) -> Result<(
    FileAnalysis,
    Vec<smt2parser::analysis::quantifier_support::AssertionAnalysis>,
)> {
    let let_path = output_root.join("let_eliminated").join(relative_path);
    let nnf_path = output_root.join("nnf").join(relative_path);
    if let Some(parent) = let_path.parent() {
        fs::create_dir_all(parent)?;
    }
    if let Some(parent) = nnf_path.parent() {
        fs::create_dir_all(parent)?;
    }
    let let_file = fs::File::create(let_path)?;
    let nnf_file = fs::File::create(nnf_path)?;
    let mut let_writer = BufWriter::new(let_file);
    let mut nnf_writer = BufWriter::new(nnf_file);

    let mut accumulator = FileAnalysisAccumulator::default();
    let mut assertions = Vec::new();

    for command in commands.iter().cloned() {
        accumulator.observe_command(&command);
        match command {
            SmtCommand::Assert { term } => {
                let processed = analyze_assertion(assertions.len(), term, options);
                writeln!(let_writer, "{}", processed.let_command)?;
                writeln!(nnf_writer, "{}", processed.nnf_command)?;
                accumulator.observe_assertion(&processed.analysis);
                assertions.push(processed.analysis);
            }
            other => {
                writeln!(let_writer, "{other}")?;
                writeln!(nnf_writer, "{other}")?;
            }
        }
    }

    let_writer.flush()?;
    nnf_writer.flush()?;
    Ok((accumulator.finish(relative_path), assertions))
}

fn write_assertion_analysis(
    output_root: &Path,
    relative_path: &Path,
    assertions: &[smt2parser::analysis::quantifier_support::AssertionAnalysis],
) -> Result<()> {
    let path = output_root.join("assertions").join(relative_path);
    let path = path.with_extension("json");
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, serde_json::to_string_pretty(assertions)?)?;
    Ok(())
}

fn write_summary(output_root: &Path, summary: &SummaryAccumulator) -> Result<()> {
    fs::write(
        output_root.join("summary.json"),
        serde_json::to_string_pretty(&summary.to_report())?,
    )?;
    Ok(())
}

fn collect_smt2_files(root: &Path) -> Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    collect_smt2_files_rec(root, &mut files)?;
    files.sort();
    Ok(files)
}

fn collect_smt2_files_rec(root: &Path, files: &mut Vec<PathBuf>) -> Result<()> {
    for entry in fs::read_dir(root)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_smt2_files_rec(&path, files)?;
        } else if matches!(
            path.extension().and_then(|ext| ext.to_str()),
            Some("smt2" | "smt")
        ) {
            files.push(path);
        }
    }
    Ok(())
}
