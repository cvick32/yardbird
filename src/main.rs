use clap::Parser;
use log::info;
use std::{fs::File, io::Write, path::Path};
use yardbird::{
    logger, model_from_options,
    problem::Problem,
    smtlib_problem::{SMTLIBProblem, SMTLIBSolver},
    strategies::{Interpolating, Repl},
    Driver, Theory, YardbirdOptions,
};

fn main() -> anyhow::Result<()> {
    logger::init_logger(log::Level::Info);
    let options = YardbirdOptions::parse();

    // Auto-detect mode based on file extension
    let path = Path::new(&options.filename);
    let extension = path.extension().and_then(|s| s.to_str());

    match extension {
        Some("smt2") => {
            // SMTLIB mode
            run_smtlib_mode(&options)?;
        }
        Some("vmt") => {
            // VMT mode (default)
            run_vmt_mode(&options)?;
        }
        _ => {
            panic!("Extension not supported: {:?}", extension)
        }
    }

    Ok(())
}

fn run_smtlib_mode(options: &YardbirdOptions) -> anyhow::Result<()> {
    info!("Running in SMTLIB mode");

    // Parse SMTLIB problem
    let problem = SMTLIBProblem::from_path(&options.filename)
        .map_err(|e| anyhow::anyhow!("Failed to parse SMTLIB file: {:?}", e))?;

    info!(
        "Parsed SMTLIB problem: {} check-sat commands, incremental: {}",
        problem.num_check_sats(),
        problem.is_incremental()
    );

    if options.print_file {
        use std::fs::File;
        use std::io::Write;
        let mut output = File::create("original.smt2").unwrap();
        let _ = output.write(problem.as_smt2_string().as_bytes());
        info!("Wrote preprocessed SMT2 to original.smt2");
    }

    // Create and execute solver
    let mut solver = SMTLIBSolver::new(problem.get_logic());
    solver.execute(&problem);

    // Print results
    let results = solver.get_results();
    if options.json_output {
        // JSON output for garden
        let json_output = serde_json::json!({
            "mode": "smtlib",
            "num_check_sats": results.len(),
            "results": results.iter().map(|r| {
                serde_json::json!({
                    "command_index": r.command_index,
                    "result": format!("{:?}", r.result),
                })
            }).collect::<Vec<_>>(),
            "statistics": solver.get_statistics(),
        });
        println!("{}", serde_json::to_string(&json_output)?);
    } else {
        // Human-readable output
        info!("SMTLIB Execution Complete!");
        info!("Check-sat results:");
        for (idx, result) in results.iter().enumerate() {
            info!(
                "  Check-sat #{} (command index {}): {:?}",
                idx + 1,
                result.command_index,
                result.result
            );
        }
        info!("Solver statistics: {:#?}", solver.get_statistics());
    }

    Ok(())
}

fn run_vmt_mode(options: &YardbirdOptions) -> anyhow::Result<()> {
    info!("Running in VMT mode");
    let vmt_model = model_from_options(options);
    let instantiation_strategy = options.build_instantiation_strategy();

    //let cfg = z3::Config::new();
    //cfg.set_proof_generation(true);
    match options.theory {
        Theory::Array => {
            let mut driver = Driver::new(vmt_model, instantiation_strategy).with_tracking_options(
                options.dump_solver.clone(),
                options.track_instantiations,
                options.dump_unsat_core.clone(),
            );
            if options.repl {
                driver.add_extension(Repl);
            }
            if options.interpolate {
                driver.add_extension(Interpolating);
            }
            let res = driver.check_strategy(options.depth, options.build_array_strategy())?;
            print_file_results(res, options)?;
        }
        Theory::BvList => {
            todo!("Implement BVList!")
        }
        Theory::List => {
            let mut driver = Driver::new(vmt_model, instantiation_strategy).with_tracking_options(
                options.dump_solver.clone(),
                options.track_instantiations,
                options.dump_unsat_core.clone(),
            );
            if options.repl {
                driver.add_extension(Repl);
            }
            if options.interpolate {
                driver.add_extension(Interpolating);
            }
            let res = driver.check_strategy(options.depth, options.build_list_strategy())?;
            print_file_results(res, options)?;
        }
    };

    Ok(())
}

fn print_file_results(
    res: impl Into<yardbird::ProofLoopResult>,
    options: &YardbirdOptions,
) -> anyhow::Result<()> {
    let res = res.into();

    if options.json_output {
        // Output JSON to stdout for garden to parse
        println!("{}", serde_json::to_string(&res)?);
    } else {
        // Normal human-readable output
        info!("SUCCESSFUL BMC!");
        info!(
            "NEEDED INSTANTIATIONS:\n{}",
            res.get_instantiations_string()
        );
        info!("TOTAL NUMBER: {}", res.total_instantiations_added);
        log::debug!("Solver stats: {:#?}", res.solver_statistics);
    }

    if let Some(model) = res.model {
        if options.print_file {
            let mut output = File::create("instantiated.vmt").unwrap();
            let _ = output.write(model.as_vmt_string().as_bytes());
        }
    }

    Ok(())
}
