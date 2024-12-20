use clap::Parser;
use log::info;
use std::{fs::File, io::Write};
use yardbird::{logger, model_from_options, Driver, YardbirdOptions};

fn main() -> anyhow::Result<()> {
    logger::init_logger();
    let options = YardbirdOptions::parse();
    let abstract_vmt_model = model_from_options(&options);
    let driver = Driver::new(&options, &z3::Config::new(), abstract_vmt_model);
    let res = driver.check_to_depth(options.depth, 10)?;

    info!("NEEDED INSTANTIATIONS: {:#?}", res.used_instances);
    if options.print_vmt {
        let mut output = File::create("instantiated.vmt").unwrap();
        let _ = output.write(res.model.as_vmt_string().as_bytes());
    }
    Ok(())
}
