#![warn(clippy::print_stdout)]

use std::{fs::File, io::Write};

use clap::{Parser, ValueEnum};
use cost_functions::array::{ast_size_cost_factory, best_symbol_cost_factory};
pub use driver::{Driver, Error, ProofLoopResult, Result};
use serde::{Deserialize, Serialize};
use smt2parser::vmt::VMTModel;
use strategies::{Abstract, AbstractRefinementState, ConcreteZ3, ListAbstract, ProofStrategy};

pub mod analysis;
pub mod conflict_scheduler;
pub mod cost_functions;
mod driver;
mod egg_utils;
mod extractor;
pub mod ic3ia;
mod interpolant;
pub mod logger;
mod proof_tree;
pub mod smt_problem;
pub mod strategies;
mod subterm_handler;
pub mod theories;
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
    pub depth: u16,

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

    // Invoke IC3IA
    #[arg(long, default_value_t = false)]
    pub run_ic3ia: bool,

    // Choose Cost Function
    #[arg(short, long, value_enum, default_value_t = CostFunction::SymbolCost)]
    pub cost_function: CostFunction,

    // Choose Language Theory
    #[arg(short, long, value_enum, default_value_t = Language::Array)]
    pub language: Language,
}

impl Default for YardbirdOptions {
    fn default() -> Self {
        YardbirdOptions {
            filename: "".into(),
            depth: 10,
            print_vmt: false,
            interpolate: false,
            strategy: Strategy::Abstract,
            repl: false,
            run_ic3ia: false,
            cost_function: CostFunction::SymbolCost,
            language: Language::Array,
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

    pub fn build_array_strategy(&self) -> Box<dyn ProofStrategy<'_, AbstractRefinementState>> {
        match self.strategy {
            Strategy::Abstract => match self.cost_function {
                CostFunction::SymbolCost => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    best_symbol_cost_factory,
                )),
                CostFunction::ASTSize => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    ast_size_cost_factory,
                )),
            },
            Strategy::Concrete => Box::new(ConcreteZ3::new(self.run_ic3ia)),
        }
    }

    pub fn build_bvlist_strategy(&self) -> Box<dyn ProofStrategy<'_, AbstractRefinementState>> {
        // For now, use the same strategy structure as arrays
        // TODO: Create proper bit-vector list strategy
        match self.strategy {
            Strategy::Abstract => match self.cost_function {
                CostFunction::SymbolCost => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    best_symbol_cost_factory,
                )),
                CostFunction::ASTSize => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    ast_size_cost_factory,
                )),
            },
            Strategy::Concrete => Box::new(ConcreteZ3::new(self.run_ic3ia)),
        }
    }
}

pub fn model_from_options(options: &YardbirdOptions) -> VMTModel {
    let mut vmt_model = VMTModel::from_path(&options.filename).unwrap();

    // Apply language-specific model configuration
    match options.language {
        Language::Array => {
            vmt_model = vmt_model
                .abstract_array_theory()
                .abstract_constants_over(options.depth);
        }
        Language::BvList => {
            // For bit-vector lists, we don't abstract array theory
            // but might need other abstractions
            vmt_model = vmt_model.abstract_constants_over(options.depth);
        }
        Language::List => {
            // For lists, we don't abstract array theory, just constants
            vmt_model = vmt_model.abstract_constants_over(options.depth);
        }
    }

    if options.print_vmt {
        let mut output = File::create("original.vmt").unwrap();
        let _ = output.write(vmt_model.as_vmt_string().as_bytes());
    }
    vmt_model
}

/// Describes the proving strategies available.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum Strategy {
    Abstract,
    Concrete,
}

/// Describes the cost functions available.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum CostFunction {
    SymbolCost,
    ASTSize,
}

/// Describes the languages available.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum Language {
    Array,
    BvList,
    List,
}
