use clap::Parser;
use log::info;
use std::{fs::File, io::Write};
use to_vmt::to_vmt;
use yardbird::{logger, proof_loop, YardbirdOptions};

#[to_vmt]
fn array_copy(a: Vec<usize>, mut b: Vec<usize>, mut i: usize, n: usize, z: usize) {
    assert!(i == 0);
    assert!(z > 0);
    assert!(z < n);
    loop {
        if i < n {
            b[i] = a[i];
            i += 1;
        } else {
            break;
        }
    }
    assert!(i >= n);
    assert!(a[z] == b[z]);
}

fn main() -> anyhow::Result<()> {
    logger::init_logger();
    let options = YardbirdOptions::parse();
    let result = proof_loop(&options)?;
    info!("NEEDED INSTANTIATIONS: {:#?}", result.used_instances);
    if options.print_vmt {
        let mut output = File::create("instantiated.vmt").unwrap();
        let _ = output.write(result.model.as_vmt_string().as_bytes());
    }
    Ok(())
}
