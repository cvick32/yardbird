use clap::Parser;
use log::info;
use std::{fs::File, io::Write, path::Path};
use yardbird::{
    logger, model_from_options,
    problem::Problem,
    smtlib_problem::{SMTLIBProblem, SMTLIBSolver},
    strategies::{ArrayRefinementState, Interpolating, ProofStrategy, Repl},
    CostFunction, Driver, Strategy, Theory, YardbirdOptions,
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
        let mut output = File::create("original.smt2").unwrap();
        let _ = output.write(problem.as_smt2_string().as_bytes());
        info!("Wrote preprocessed SMT2 to original.smt2");
    }

    // Detect if we should use strategy mode
    let use_strategy = should_use_strategy_mode(options);

    if use_strategy {
        info!(
            "Using strategy-based solving: strategy={}, cost-function={}",
            options.strategy, options.cost_function
        );
        run_smtlib_with_strategy(&problem, options)?;
    } else {
        info!("Using simple mode (no refinement)");
        run_smtlib_simple(&problem, options)?;
    }

    Ok(())
}

/// Determine if we should use strategy-based solving
fn should_use_strategy_mode(options: &YardbirdOptions) -> bool {
    // Use strategy mode if:
    // 1. Strategy is not Concrete (Abstract strategies need refinement)
    // 2. Cost function is not BmcCost (indicates user wants specific cost function)
    !matches!(options.strategy, Strategy::Concrete)
        || !matches!(options.cost_function, CostFunction::BmcCost)
}

/// Run SMTLIB with strategy-based refinement
fn run_smtlib_with_strategy(
    problem: &SMTLIBProblem,
    options: &YardbirdOptions,
) -> anyhow::Result<()> {
    let strategy = build_smtlib_strategy(options);
    //let instantiation_strategy = options.build_instantiation_strategy();

    let (result, abstracted_problem) = SMTLIBSolver::execute_with_strategy(
        problem, strategy,
        250, // max refinements (like VMT mode)
            //instantiation_strategy,
    )?;

    // Print abstracted output if requested
    if options.print_file {
        if let Some(abs_problem) = abstracted_problem {
            let mut output = File::create("abstracted.smt2")?;
            let _ = output.write(abs_problem.as_smt2_string().as_bytes());
            info!("Wrote abstracted SMT2 to abstracted.smt2");
        }
    }

    print_strategy_results(&result, options)?;
    Ok(())
}

/// Run SMTLIB in simple mode (no refinement)
fn run_smtlib_simple(problem: &SMTLIBProblem, options: &YardbirdOptions) -> anyhow::Result<()> {
    let mut solver = SMTLIBSolver::new(problem.get_logic());
    solver.execute(problem);

    let results = solver.get_results();
    if options.json_output {
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

/// Build a strategy for SMTLIB mode based on options
fn build_smtlib_strategy(
    options: &YardbirdOptions,
) -> Box<dyn ProofStrategy<'static, ArrayRefinementState>> {
    use yardbird::cost_functions::array::*;
    use yardbird::strategies::{Abstract, AbstractArrayWithQuantifiers, ConcreteArrayZ3};

    match options.strategy {
        Strategy::Abstract => match options.cost_function {
            CostFunction::BmcCost => Box::new(Abstract::new(
                0, // depth=0 for SMTLIB (no temporal unrolling)
                options.run_ic3ia,
                array_bmc_cost_factory,
            )),
            CostFunction::AstSize => Box::new(Abstract::new(
                0,
                options.run_ic3ia,
                array_ast_size_cost_factory,
            )),
            CostFunction::AdaptiveCost => Box::new(Abstract::new(
                0,
                options.run_ic3ia,
                adaptive_array_cost_factory,
            )),
            CostFunction::SplitCost => Box::new(Abstract::new(
                0,
                options.run_ic3ia,
                split_array_cost_factory,
            )),
            CostFunction::PreferRead => Box::new(Abstract::new(
                0,
                options.run_ic3ia,
                array_prefer_read_factory,
            )),
            CostFunction::PreferWrite => Box::new(Abstract::new(
                0,
                options.run_ic3ia,
                array_prefer_write_factory,
            )),
            CostFunction::PreferConstants => {
                Box::new(Abstract::new(0, options.run_ic3ia, array_prefer_constants))
            }
        },
        Strategy::AbstractWithQuantifiers => {
            Box::new(AbstractArrayWithQuantifiers::new(options.run_ic3ia))
        }
        Strategy::Concrete => Box::new(ConcreteArrayZ3::new(options.run_ic3ia)),
    }
}

/// Print results from strategy-based solving
fn print_strategy_results(
    result: &yardbird::ProofLoopResult,
    options: &YardbirdOptions,
) -> anyhow::Result<()> {
    if options.json_output {
        println!("{}", serde_json::to_string(result)?);
    } else {
        info!("Strategy-based solving complete!");
        info!(
            "Total instantiations added: {}",
            result.total_instantiations_added
        );
        info!("Used instances: {}", result.used_instances.len());
        info!("Const instances: {}", result.const_instances.len());
        info!("Found proof: {}", result.found_proof);
        info!("Found counterexample: {}", result.counterexample);
        log::debug!("Solver statistics: {:#?}", result.solver_statistics);
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
