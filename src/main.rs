use std::{fs::File, io::Write};

use clap::Parser;
use log::info;
use yardbird::{
    logger, model_from_options,
    strategies::{Interpolating, Repl},
    Driver, ProofLoopResultType, YardbirdOptions,
};

fn main() -> anyhow::Result<()> {
    logger::init_logger(log::Level::Info);
    let options = YardbirdOptions::parse();
    let vmt_model = model_from_options(&options);

    let cfg = z3::Config::new();
    let context = z3::Context::new(&cfg);
    let mut driver = Driver::new(&context, vmt_model);

    // build the strategy
    let strat = options.build_strategy();

    // build up set of extensions based on command line options
    if options.repl {
        driver.add_extension(Repl);
    }

    if options.interpolate {
        driver.add_extension(Interpolating);
    }

    let res = driver.check_strategy(options.depth, strat)?;

    match res.result_type {
        ProofLoopResultType::Success => {
            info!("SUCCESSFUL BMC!");
            info!("NEEDED INSTANTIATIONS: {:#?}", res.used_instances);
        }
        ProofLoopResultType::NoProgress => {
            info!("NO PROGRESS!");
            info!("USED INSTANTIATIONS: {:#?}", res.used_instances);
        }
    }

    if options.print_vmt {
        if let Some(model) = res.model {
            let mut output = File::create("instantiated.vmt").unwrap();
            let _ = output.write(model.as_vmt_string().as_bytes());
        }
    }

    Ok(())
}
