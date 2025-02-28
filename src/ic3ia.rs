use std::io::Write;

use smt2parser::vmt::VMTModel;
use tempfile::NamedTempFile;

use crate::utils;

use log;

pub fn call_ic3ia(model: VMTModel) -> Result<String, String> {
    let mut temp_file = NamedTempFile::new().unwrap();

    let _ = temp_file.write(model.as_vmt_string().as_bytes());

    // invoke IC3IA
    let path = temp_file.path().to_str().unwrap();
    log::info!("CALLING IC3IA ON TEMPORARY FILE.");

    utils::run_command("ic3ia", &[path, "-w"])
}
