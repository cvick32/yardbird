use std::{fs::File, io::Write};

use clap::Parser;
use log::info;
use yardbird::{
    logger, model_from_options,
    strategies::{Abstract, ConcreteZ3, Interpolating, ProofStrategy, Repl},
    Driver, DriverExtensions, YardbirdOptions,
};

fn main() -> anyhow::Result<()> {
    logger::init_logger();
    let options = YardbirdOptions::parse();
    let vmt_model = model_from_options(&options);

    let mut driver = Driver::new(&options, &z3::Config::new(), vmt_model);

    // build the strategy
    let strat: Box<dyn ProofStrategy<_>> = match options.strategy {
        yardbird::Strategy::Abstract => Box::new(Abstract::default()),
        yardbird::Strategy::Concrete => Box::new(ConcreteZ3::default()),
    };

    let mut extensions = DriverExtensions::default();
    if options.interactive {
        extensions.add_extension(Repl);
    }

    if options.interpolate {
        extensions.add_extension(Interpolating);
    }

    let res = driver.check_strategy(options.depth, strat, &mut extensions)?;

    info!("NEEDED INSTANTIATIONS: {:#?}", res.used_instances);
    if options.print_vmt {
        if let Some(model) = res.model {
            let mut output = File::create("instantiated.vmt").unwrap();
            let _ = output.write(model.as_vmt_string().as_bytes());
        }
    }

    Ok(())
}
