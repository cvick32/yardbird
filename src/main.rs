use clap::Parser;
use log::info;
use std::{fs::File, io::Write};
use yardbird::{logger, model_from_options, proof_loop, YardbirdOptions};

fn main() -> anyhow::Result<()> {
    logger::init_logger();
    let options = YardbirdOptions::parse();
    let abstract_vmt_model = model_from_options(&options);
    let result = proof_loop(&options, abstract_vmt_model)?;
    info!("NEEDED INSTANTIATIONS: {:#?}", result.used_instances);
    if options.print_vmt {
        let mut output = File::create("instantiated.vmt").unwrap();
        let _ = output.write(result.model.as_vmt_string().as_bytes());
    }
    Ok(())
}
