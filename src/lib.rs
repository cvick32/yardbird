use std::{cmp, fs::File, io::Write};

use crate::analysis::SaturationInequalities;
use anyhow::anyhow;
use array_axioms::ArrayLanguage;
use clap::Parser;
use egg_utils::Saturate;
use itertools::Itertools;
use log::{debug, info};
use smt2parser::vmt::VMTModel;
use utils::run_smtinterpol;
use z3::{Config, Context, Solver};
use z3_var_context::Z3VarContext;

pub mod analysis;
pub mod array_axioms;
pub mod conflict_scheduler;
mod cost;
mod egg_utils;
mod interpolant;
pub mod logger;
mod utils;
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
}

impl Default for YardbirdOptions {
    fn default() -> Self {
        YardbirdOptions {
            filename: "".into(),
            depth: 10,
            bmc_count: 1,
            print_vmt: false,
            interpolate: false,
        }
    }
}

#[derive(Debug)]
pub struct ProofLoopResult {
    pub model: VMTModel,
    pub used_instances: Vec<String>,
    pub const_instances: Vec<String>,
}

/// The main verification loop.
pub fn proof_loop(
    options: &YardbirdOptions,
    mut vmt_model: VMTModel,
) -> anyhow::Result<ProofLoopResult> {
    let mut used_instances = vec![];
    let mut const_instances = vec![];
    let config: Config = Config::new();
    let context: Context = Context::new(&config);
    for depth in 0..50 {
        info!("STARTING BMC FOR DEPTH {}", depth);
        for _ in 0..10 {
            // Run max of 10 iterations for depth
            // Currently run once, this will eventually run until UNSAT
            let smt = vmt_model.unroll(depth);
            let z3_var_context = Z3VarContext::from(&context, &smt);
            let solver = Solver::new(&context);
            solver.from_string(smt.to_bmc());
            // debug!("smt2lib program:\n{}", smt.to_bmc());
            // TODO: abstract this out somehow
            let mut egraph: egg::EGraph<ArrayLanguage, _> =
                egg::EGraph::new(SaturationInequalities).with_explanations_enabled();
            for term in smt.get_assert_terms() {
                egraph.add_expr(&term.parse()?);
            }
            match solver.check() {
                z3::SatResult::Unsat => {
                    info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", depth);
                    if options.interpolate {
                        let interpolants = run_smtinterpol(smt);
                        match interpolants {
                            Ok(_interps) => println!("{:#?}", _interps),
                            Err(err) => println!("Error when computing interpolants: {err}"),
                        }
                    }
                    break;
                }
                z3::SatResult::Unknown => {
                    // CV: I've seen Z3 return unknown then re-run Z3 and gotten SAT or UNSAT.
                    // This might be a place to retry at least once before panicking.
                    panic!("Z3 RETURNED UNKNOWN!");
                }
                z3::SatResult::Sat => {
                    // find Array theory fact that rules out counterexample
                    let model = solver.get_model().ok_or(anyhow!("No z3 model"))?;
                    debug!("model:\n{}", sort_model(&model)?);
                    update_egraph_from_model(&mut egraph, &model)?;
                    update_egraph_with_non_array_function_terms(
                        &mut egraph,
                        smt,
                        &z3_var_context,
                        &model,
                    )?;
                    egraph.rebuild();
                    let (instantiations, const_instantiations) = egraph.saturate();
                    const_instances.extend_from_slice(&const_instantiations);

                    // add all instantiations to the model,
                    // if we have already seen all instantiations, break
                    // TODO: not sure if this is correct...
                    let no_progress = instantiations
                        .into_iter()
                        .all(|inst| !vmt_model.add_instantiation(inst, &mut used_instances));
                    if no_progress {
                        return Err(anyhow!("Failed to add new instantations"));
                    }
                }
            }
        }
    }
    Ok(ProofLoopResult {
        model: vmt_model,
        used_instances,
        const_instances,
    })
}

fn sort_model(model: &z3::Model) -> anyhow::Result<String> {
    let mut b = String::new();
    for func_decl in model.iter().sorted_by(func_decl_sort) {
        if func_decl.arity() == 0 {
            // VARIABLE
            // Apply no arguments to the constant so we can call get_const_interp.
            let func_decl_ast = func_decl.apply(&[]);
            let var_name = func_decl.name();
            let value = model.get_const_interp(&func_decl_ast).ok_or(anyhow!(
                "Could not find interpretation for variable: {func_decl}"
            ))?;
            b.push_str(&format!("{var_name} -> {value}\n"));
        } else {
            // FUNCTION DEF
            let interpretation = model
                .get_func_interp(&func_decl)
                .ok_or(anyhow!("No function interpretation for: {func_decl}"))?;
            // b.push_str(&format!("{interpretation}\n"))
            for entry in interpretation.get_entries() {
                let function_call = format!(
                    "{} {}",
                    func_decl.name(),
                    entry
                        .get_args()
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(" ")
                );
                let value = entry.get_value().to_string();
                b.push_str(&format!("{function_call} -> {value}\n"));
            }
        }
    }
    // let model_string = format!("{model}");
    Ok(b)
}

fn func_decl_sort(a: &z3::FuncDecl, b: &z3::FuncDecl) -> cmp::Ordering {
    let arity_cmp = a.arity().cmp(&b.arity());
    if !matches!(arity_cmp, cmp::Ordering::Equal) {
        return a.name().cmp(&b.name());
    }

    let a_name = a.name();
    let b_name = b.name();
    let a_parts = a_name.split_once("@");
    let b_parts = b_name.split_once("@");

    match (a_parts, b_parts) {
        (None, None) => cmp::Ordering::Equal,
        (Some(_), None) => cmp::Ordering::Greater,
        (None, Some(_)) => cmp::Ordering::Less,
        (Some((av, an)), Some((bv, bn))) => match av.cmp(bv) {
            cmp::Ordering::Equal => {
                let au32 = an.parse::<u32>().unwrap();
                let bu32 = bn.parse::<u32>().unwrap();
                au32.cmp(&bu32)
            }
            x @ (cmp::Ordering::Less | cmp::Ordering::Greater) => x,
        },
    }
}

/// This function adds terms into the Egraph from the SMTProblem
/// that are not explicitly listed in the model. For instance,
/// in `array_copy_increment.vmt`, the term (+ 1 (Read a i))
/// will never be added to the egraph because it's neither a
/// constant nor a direct application of an Array function. We
/// still want these terms in the Egraph so that we can substitute
/// them in for constants.
fn update_egraph_with_non_array_function_terms<'ctx>(
    egraph: &mut egg::EGraph<ArrayLanguage, SaturationInequalities>,
    smt: smt2parser::vmt::smt::SMTProblem,
    z3_var_context: &'ctx Z3VarContext<'ctx>,
    model: &z3::Model<'ctx>,
) -> anyhow::Result<()> {
    for term in smt.get_eq_terms() {
        let term_id = egraph.add_expr(&term.to_string().parse()?);
        let z3_term = z3_var_context.rewrite_term(&term);
        let model_interp = model
            .eval(&z3_term, false)
            .unwrap_or_else(|| panic!("Term not found in model: {term}"));
        let interp_id = egraph.add_expr(&model_interp.to_string().parse()?);
        info!("Adding: {} = {}", term, model_interp);
        egraph.union(term_id, interp_id);
        egraph.rebuild();
    }
    Ok(())
}

/// Add variable and Array function interpretations into the egraph.
fn update_egraph_from_model(
    egraph: &mut egg::EGraph<ArrayLanguage, SaturationInequalities>,
    model: &z3::Model<'_>,
) -> anyhow::Result<()> {
    for func_decl in model.iter().sorted_by(func_decl_sort) {
        if func_decl.arity() == 0 {
            // VARIABLE
            // Apply no arguments to the constant so we can call get_const_interp.
            let func_decl_ast = func_decl.apply(&[]);
            let var = func_decl.name().parse()?;
            let var_id = egraph.add_expr(&var);
            let value = model.get_const_interp(&func_decl_ast).ok_or(anyhow!(
                "Could not find interpretation for variable: {func_decl}"
            ))?;
            let expr = value.to_string().parse()?;
            let value_id = egraph.add_expr(&expr);
            egraph.union(var_id, value_id);
        } else {
            // FUNCTION DEF
            let interpretation = model
                .get_func_interp(&func_decl)
                .ok_or(anyhow!("No function interpretation for: {func_decl}"))?;
            for entry in interpretation.get_entries() {
                let function_call = format!(
                    "({} {})",
                    func_decl.name(),
                    entry
                        .get_args()
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(" ")
                );
                let funcall = function_call.parse()?;
                let expr = entry.get_value().to_string().parse()?;
                let function_id = egraph.add_expr(&funcall);
                let value_id = egraph.add_expr(&expr);
                egraph.union(function_id, value_id);
            }
        }
        egraph.rebuild();
    }
    Ok(())
}

pub fn model_from_options(options: &YardbirdOptions) -> VMTModel {
    let concrete_vmt_model = VMTModel::from_path(&options.filename).unwrap();
    let abstract_vmt_model = concrete_vmt_model.abstract_array_theory();
    if options.print_vmt {
        let mut output = File::create("original.vmt").unwrap();
        let _ = output.write(abstract_vmt_model.as_vmt_string().as_bytes());
    }
    abstract_vmt_model
}
