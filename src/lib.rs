#![warn(clippy::print_stdout)]

use std::{fs::File, io::Write};

use clap::{Parser, ValueEnum};
pub use driver::{Driver, Error, ProofLoopResult, Result};
use serde::Serialize;
use smt2parser::vmt::VMTModel;
use strategies::{Abstract, AbstractOnlyBest, AbstractRefinementState, ConcreteZ3, ProofStrategy};

pub mod analysis;
pub mod array_axioms;
pub mod conflict_scheduler;
mod cost_functions;
mod driver;
mod egg_utils;
mod extractor;
mod interpolant;
pub mod logger;
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
    pub repl: bool,
    /// Show line number in log
    #[arg(long, default_value_t = false)]
    pub line_numbers: bool,
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
            repl: false,
            line_numbers: false,
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

    pub fn build_strategy(&self) -> Box<dyn ProofStrategy<AbstractRefinementState>> {
        match self.strategy {
            Strategy::Abstract => Box::new(Abstract::new(self.depth)),
            Strategy::AbstractOnlyBest => Box::new(AbstractOnlyBest::new(self.depth)),
            Strategy::Concrete => Box::new(ConcreteZ3::default()),
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
#[derive(Copy, Clone, Debug, ValueEnum, Serialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum Strategy {
    Abstract,
    AbstractOnlyBest,
    Concrete,
}
