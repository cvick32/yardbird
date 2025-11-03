#![warn(clippy::print_stdout)]

use std::{fmt::Display, fs::File, io::Write};

use clap::{Parser, ValueEnum};
pub use driver::{Driver, Error, ProofLoopResult, Result};
use serde::{Deserialize, Serialize};
use smt2parser::vmt::VMTModel;
use strategies::{
    Abstract, AbstractArrayWithQuantifiers, ArrayRefinementState, ConcreteArrayZ3, ListAbstract,
    ProofStrategy,
};

use crate::{
    cost_functions::{
        array::{
            adaptive_array_cost_factory, array_ast_size_cost_factory,
            array_best_symbol_cost_factory, array_prefer_constants, array_prefer_read_factory,
            array_prefer_write_factory, split_array_cost_factory,
        },
        list::list_ast_size_cost_factory,
    },
    strategies::ListRefinementState,
};

pub mod analysis;
pub mod baml_client;
pub mod cost_functions;
mod driver;
mod egg_utils;
pub mod ic3ia;
mod interpolant;
pub mod logger;
mod proof_tree;
pub mod smt_problem;
pub mod strategies;
mod subterm_handler;
pub mod theories;
pub mod theory_support;
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

    // Choose Theory
    #[arg(short, long, value_enum, default_value_t = Theory::Array)]
    pub theory: Theory,

    /// Output ProofLoopResult as JSON to stdout (for garden integration)
    #[arg(long, default_value_t = false)]
    pub json_output: bool,

    /// Dump solver state to SMT2 file when unsat is reached
    #[arg(long)]
    pub dump_solver: Option<String>,

    /// Track instantiations using Z3's assert-and-track for unsat core analysis
    #[arg(long, default_value_t = false)]
    pub track_instantiations: bool,

    /// Dump unsat core to JSON file when tracking is enabled and unsat is reached
    #[arg(long)]
    pub dump_unsat_core: Option<String>,
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
            theory: Theory::Array,
            json_output: false,
            dump_solver: None,
            track_instantiations: false,
            dump_unsat_core: None,
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

    pub fn build_array_strategy(&self) -> Box<dyn ProofStrategy<'_, ArrayRefinementState>> {
        match self.strategy {
            Strategy::Abstract => match self.cost_function {
                CostFunction::SymbolCost => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    array_best_symbol_cost_factory,
                )),
                CostFunction::ASTSize => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    array_ast_size_cost_factory,
                )),
                CostFunction::AdaptiveCost => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    adaptive_array_cost_factory,
                )),
                CostFunction::SplitCost => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    split_array_cost_factory,
                )),
                CostFunction::PreferRead => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    array_prefer_read_factory,
                )),
                CostFunction::PreferWrite => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    array_prefer_write_factory,
                )),
                CostFunction::PreferConstants => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    array_prefer_constants,
                )),
            },
            Strategy::AbstractWithQuantifiers => {
                Box::new(AbstractArrayWithQuantifiers::new(self.run_ic3ia))
            }
            Strategy::Concrete => Box::new(ConcreteArrayZ3::new(self.run_ic3ia)),
        }
    }

    pub fn build_bvlist_strategy(&self) -> Box<dyn ProofStrategy<'_, ArrayRefinementState>> {
        // For now, use the same strategy structure as arrays
        // TODO: Create proper bit-vector list strategy
        match self.strategy {
            Strategy::Abstract => match self.cost_function {
                CostFunction::SymbolCost => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    array_best_symbol_cost_factory,
                )),
                CostFunction::ASTSize => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    array_ast_size_cost_factory,
                )),
                CostFunction::AdaptiveCost => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    adaptive_array_cost_factory,
                )),
                CostFunction::SplitCost => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    split_array_cost_factory,
                )),
                CostFunction::PreferRead => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    array_prefer_read_factory,
                )),
                CostFunction::PreferWrite => Box::new(Abstract::new(
                    self.depth,
                    self.run_ic3ia,
                    array_prefer_write_factory,
                )),
                CostFunction::PreferConstants => todo!(),
            },
            Strategy::AbstractWithQuantifiers => {
                Box::new(AbstractArrayWithQuantifiers::new(self.run_ic3ia))
            }
            Strategy::Concrete => Box::new(ConcreteArrayZ3::new(self.run_ic3ia)),
        }
    }

    pub fn build_list_strategy(&self) -> Box<dyn ProofStrategy<'_, ListRefinementState>> {
        match self.strategy {
            Strategy::Abstract => match self.cost_function {
                CostFunction::SymbolCost => todo!(),
                CostFunction::ASTSize => Box::new(ListAbstract::new(
                    self.depth,
                    self.run_ic3ia,
                    list_ast_size_cost_factory,
                )),
                CostFunction::AdaptiveCost => todo!(),
                CostFunction::SplitCost => todo!(),
                CostFunction::PreferRead => todo!(),
                CostFunction::PreferWrite => todo!(),
                CostFunction::PreferConstants => todo!(),
            },
            Strategy::AbstractWithQuantifiers => {
                todo!("AbstractWithQuantifiers not yet implemented for List theory")
            }
            Strategy::Concrete => {
                todo!()
            }
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
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum Strategy {
    Abstract,
    AbstractWithQuantifiers,
    Concrete,
}

impl Display for Strategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Strategy::Abstract => write!(f, "abstract"),
            Strategy::AbstractWithQuantifiers => write!(f, "abstract-with-quantifiers"),
            Strategy::Concrete => write!(f, "concrete"),
        }
    }
}

/// Describes the cost functions available.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum CostFunction {
    SymbolCost,
    ASTSize,
    AdaptiveCost,
    SplitCost,
    PreferRead,
    PreferWrite,
    PreferConstants,
}

impl Display for CostFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CostFunction::SymbolCost => write!(f, "symbol-cost"),
            CostFunction::ASTSize => write!(f, "ast-size"),
            CostFunction::AdaptiveCost => write!(f, "adaptive-cost"),
            CostFunction::SplitCost => write!(f, "split-cost"),
            CostFunction::PreferRead => write!(f, "prefer-read"),
            CostFunction::PreferWrite => write!(f, "prefer-write"),
            CostFunction::PreferConstants => write!(f, "prefer-constants"),
        }
    }
}

/// Describes the theories available.
#[derive(Copy, Clone, Debug, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum Theory {
    Array,
    BvList,
    List,
}
