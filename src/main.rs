use clap::Parser;
use log::info;
use std::{fs::File, io::Write};
use yardbird::{
    logger, model_from_options,
    strategies::{Interpolating, Repl},
    Driver, Theory, YardbirdOptions,
};

fn main() -> anyhow::Result<()> {
    logger::init_logger(log::Level::Info);
    let options = YardbirdOptions::parse();
    let vmt_model = model_from_options(&options);

    let cfg = z3::Config::new();
    //cfg.set_proof_generation(true);
    let context = z3::Context::new(&cfg);
    match options.theory {
        Theory::Array => {
            let mut driver = Driver::new(&context, vmt_model).with_tracking_options(
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
            print_results(res, &options)?;
        }
        Theory::BvList => {
            todo!("Implement BVList!")
        }
        Theory::List => {
            let mut driver = Driver::new(&context, vmt_model).with_tracking_options(
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
            print_results(res, &options)?;
        }
    };

    Ok(())
}

fn print_results(
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
        if options.print_vmt {
            let mut output = File::create("instantiated.vmt").unwrap();
            let _ = output.write(model.as_vmt_string().as_bytes());
        }
    }

    Ok(())
}
