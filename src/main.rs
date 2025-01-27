use std::{fs::File, io::Write};

use clap::Parser;
use itertools::Itertools;
use log::info;
use yardbird::{
    logger, model_from_options,
    strategies::{Interpolating, Minify, Repl},
    Driver, YardbirdOptions,
};

fn main() -> anyhow::Result<()> {
    logger::init_logger(log::Level::Info);
    let options = YardbirdOptions::parse();
    let vmt_model = model_from_options(&options);

    let cfg = z3::Config::new();
    let context = z3::Context::new(&cfg);
    let mut driver = Driver::new(&context, vmt_model.clone());

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

    info!("SUCCESSFUL BMC!");
    info!(
        "USED INSTANTIATIONS:\n{}",
        res.used_instances
            .iter()
            .map(|inst| format!(" - {inst}"))
            .join("\n")
    );

    if options.minify {
        log::set_max_level(log::LevelFilter::Off);
        let necessary = Minify::minify(vmt_model.clone(), res.used_instances, options.depth);
        println!(
            "Necessary:\n{}",
            necessary.iter().map(|inst| format!(" - {inst}")).join("\n")
        );
    }

    if options.print_vmt {
        if let Some(model) = res.model {
            let mut output = File::create("instantiated.vmt").unwrap();
            let _ = output.write(model.as_vmt_string().as_bytes());
        }
    }

    Ok(())
}
