use clap::Parser;
use log::info;
use std::{fs::File, io::Write};
use yardbird::{
    logger, model_from_options,
    strategies::{Interpolating, Repl},
    Driver, Language, YardbirdOptions,
};

fn main() -> anyhow::Result<()> {
    logger::init_logger(log::Level::Info);
    let options = YardbirdOptions::parse();
    let vmt_model = model_from_options(&options);

    let cfg = z3::Config::new();
    //cfg.set_proof_generation(true);

    let context = z3::Context::new(&cfg);

    // Handle different languages
    match options.language {
        Language::Array => {
            let mut driver = Driver::new(&context, vmt_model);
            let strat = options.build_array_strategy();

            // build up set of extensions based on command line options
            if options.repl {
                driver.add_extension(Repl);
            }
            if options.interpolate {
                driver.add_extension(Interpolating);
            }

            let res = driver.check_strategy(options.depth, strat)?;
            print_results(res, &options)?;
        }
        Language::BvList => {
            println!("BitVector-List language selected!");
            println!("Note: Full implementation in progress. Using array strategy for now.");
            println!("Created benchmark files: bvlist_crypto_shuffle.vmt, bvlist_packet_filter.vmt, bvlist_error_correction.vmt");

            let mut driver = Driver::new(&context, vmt_model);
            let strat = options.build_bvlist_strategy();

            // Extensions work the same way for any language
            if options.repl {
                driver.add_extension(Repl);
            }
            if options.interpolate {
                driver.add_extension(Interpolating);
            }

            let res = driver.check_strategy(options.depth, strat)?;
            print_results(res, &options)?;
        }
    }

    Ok(())
}

fn print_results(
    res: impl Into<yardbird::ProofLoopResult>,
    options: &YardbirdOptions,
) -> anyhow::Result<()> {
    let res = res.into();
    info!("SUCCESSFUL BMC!");
    info!(
        "NEEDED INSTANTIATIONS:\n{}",
        res.get_instantiations_string()
    );
    log::debug!("Solver stats: {:#?}", res.solver_statistics);

    if let Some(model) = res.model {
        if options.print_vmt {
            let mut output = File::create("instantiated.vmt").unwrap();
            let _ = output.write(model.as_vmt_string().as_bytes());
        }
    }

    Ok(())
}
