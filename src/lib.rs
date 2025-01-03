use std::{fs::File, io::Write};

use clap::{Parser, ValueEnum};
pub use driver::{Driver, DriverExtensions, ProofLoopResult};
use smt2parser::vmt::VMTModel;

pub mod analysis;
pub mod array_axioms;
pub mod conflict_scheduler;
mod cost;
mod driver;
mod egg_utils;
mod interpolant;
pub mod logger;
pub mod repl;
pub mod strategies;
mod utils;
pub mod z3_ext;
mod z3_var_context;

#[derive(Parser, Debug, Clone)]
#[command(version, about, long_about = None)]
pub struct YardbirdOptions {
    /// Name of the VMT file.
    #[arg(short, long)]
    pub filename: String,

    /// BMC depth until quitting.
    #[arg(short, long, default_value_t = 10)]
    pub depth: u8,

    /// How many times BMC should be UNSAT until we check with an invariant generator.
    #[arg(short, long, default_value_t = 1)]
    pub bmc_count: usize,

    /// Output VMT files before and after instantiation.
    #[arg(short, long, default_value_t = false)]
    pub print_vmt: bool,

    /// Run SMTInterpol when BMC depth is UNSAT
    #[arg(short, long, default_value_t = false)]
    pub interpolate: bool,

    #[arg(short, long, value_enum, default_value_t = Strategy::Abstract)]
    pub strategy: Strategy,

    /// Interactive mode.
    #[arg(long, default_value_t = false)]
    pub interactive: bool,
}

impl Default for YardbirdOptions {
    fn default() -> Self {
        YardbirdOptions {
            filename: "".into(),
            depth: 10,
            bmc_count: 1,
            print_vmt: false,
            interpolate: false,
            strategy: Strategy::Abstract,
            interactive: false,
        }
    }
}

impl YardbirdOptions {
    pub fn from_filename(filename: String) -> Self {
        YardbirdOptions {
            filename,
            ..Default::default()
        }
    }
}

pub fn model_from_options(options: &YardbirdOptions) -> VMTModel {
    let vmt_model = VMTModel::from_path(&options.filename).unwrap();
    if options.print_vmt {
        let mut output = File::create("original.vmt").unwrap();
        let _ = output.write(vmt_model.as_vmt_string().as_bytes());
    }
    vmt_model
}

/// Describes the proving strategies available.
#[derive(Clone, Debug, ValueEnum)]
#[clap(rename_all = "kebab_case")]
pub enum Strategy {
    Abstract,
    Concrete,
}
