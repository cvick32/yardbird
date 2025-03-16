use std::io::Write;

use smt2parser::vmt::VMTModel;
use tempfile::NamedTempFile;

use crate::utils;
use std::io::Error;

use log;

pub fn call_ic3ia(model: VMTModel) -> Result<String, Error> {
    log::info!("Calling IC3IA ...");

    let mut temp_file = NamedTempFile::new().unwrap();

    let _ = temp_file.write(model.as_vmt_string().as_bytes());

    // invoke IC3IA
    let path = temp_file.path().to_str().unwrap();

    log::info!("invoking IC3IA on file {path}");

    utils::run_command("ic3ia", &[path, "-w"])
}

pub fn ic3ia_output_contains_proof(ic3ia_out: String) -> bool {
    ic3ia_out.contains("invariant")
}
