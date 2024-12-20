use clap::Parser;
use log::info;
use std::{fs::File, io::Write};
use yardbird::{concrete_z3_bmc, logger, model_from_options, Driver, YardbirdOptions};

fn main() -> anyhow::Result<()> {
    logger::init_logger();
    let options = YardbirdOptions::parse();
    let vmt_model = model_from_options(&options);
    if options.z3 {
        let _ = concrete_z3_bmc(&options, vmt_model);
    } else {
        let driver = Driver::new(&options, &z3::Config::new(), vmt_model);
        let res = driver.check_to_depth(options.depth, 10)?;
        info!("NEEDED INSTANTIATIONS: {:#?}", res.used_instances);
        if options.print_vmt {
            let mut output = File::create("instantiated.vmt").unwrap();
            let _ = output.write(res.model.as_vmt_string().as_bytes());
        }
    }
    Ok(())
}
