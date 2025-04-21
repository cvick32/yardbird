use itertools::Itertools;
use log::info;
use serde::{ser::SerializeStruct, Serialize};
use smt2parser::{concrete::Term, vmt::VMTModel};

use crate::{
    smt_problem::SMTProblem,
    strategies::{ProofAction, ProofStrategy, ProofStrategyExt},
    utils::SolverStatistics,
};

#[derive(Debug, Default)]
pub struct ProofLoopResult {
    pub model: Option<VMTModel>,
    pub used_instances: Vec<Term>,
    pub const_instances: Vec<Term>,
    pub solver_statistics: SolverStatistics,
    pub counterexample: bool,
    pub found_proof: bool,
}

impl ProofLoopResult {
    pub fn get_instantiations_string(&self) -> String {
        self.used_instances
            .iter()
            .map(|inst| format!(" - {inst}"))
            .join("\n")
    }
}

impl Serialize for ProofLoopResult {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        // 3 is the number of fields in the struct.
        let mut state = serializer.serialize_struct("ProofLoopResult", 5)?;
        state.serialize_field(
            "used_instances",
            &self
                .used_instances
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
        )?;
        state.serialize_field(
            "const_instances",
            &self
                .const_instances
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
        )?;
        state.serialize_field("solver_statistics", &self.solver_statistics)?;
        state.serialize_field("counterexample", &self.counterexample)?;
        state.serialize_field("found_proof", &self.found_proof)?;
        state.end()
    }
}

#[derive(Debug)]
pub struct Driver<'ctx, S> {
    pub used_instances: Vec<Term>,
    pub const_instances: Vec<Term>,
    pub vmt_model: VMTModel,
    context: &'ctx z3::Context,
    extensions: DriverExtensions<'ctx, S>,
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Found counter-example")]
    Counterexample,

    #[error(
        "No progress at depth {depth}\nUsed Instantiations:\n{insts}",
        insts = instantiations
            .iter()
            .map(|inst| format!(" - {inst}"))
            .join("\n")
    )]
    NoProgress {
        depth: u16,
        instantiations: Vec<Term>,
    },

    #[error("Hit refinement limit of {n_refines} at depth {depth}")]
    TooManyRefinements { n_refines: u32, depth: u16 },

    #[error("Error: {0}")]
    Anyhow(#[from] anyhow::Error),

    #[error("Solver returned unknown: {0:?}")]
    SolverUnknown(Option<String>),

    #[error("Unable to parse into e-graph: {0}")]
    RecExpr(#[from] egg::RecExprParseError<egg::FromOpError>),
}

pub type Result<T> = std::result::Result<T, Error>;

impl<'ctx, S> Driver<'ctx, S> {
    pub fn new(context: &'ctx z3::Context, vmt_model: VMTModel) -> Self {
        Self {
            used_instances: vec![],
            const_instances: vec![],
            vmt_model,
            context,
            extensions: DriverExtensions::default(),
        }
    }

    pub fn add_extension(&mut self, ext: impl ProofStrategyExt<S> + 'ctx) -> &mut Self {
        self.extensions.add_extension(ext);
        self
    }

    /// The main control flow of the proof loop.
    ///
    /// We loop up until the `target_depth`. For each of these BMC loops, we loop up to
    /// `n_refines` times. Each time, we unroll the `vmt_model` up to the current depth,
    /// ask the solver if we have any counter-examples this loop, and then continue.
    ///
    /// The `ProofStrategy` specified by `stat` defines what we do in the case of the
    /// model returning `Unsat`, `Unknown`, and `Sat`.
    pub fn check_strategy(
        &mut self,
        target_depth: u16,
        mut strat: Box<dyn ProofStrategy<'ctx, S>>,
    ) -> Result<ProofLoopResult> {
        self.vmt_model = strat.configure_model(self.vmt_model.clone());
        let n_refines = strat.n_refines();

        let mut smt_problem =
            crate::smt_problem::SMTProblem::new(&self.vmt_model, self.context, &strat);

        'bmc: for depth in 0..target_depth {
            info!("STARTING BMC FOR DEPTH {depth}");
            for i in 0..n_refines {
                info!("  refining loop: {}/{n_refines}", i + 1);
                smt_problem.unroll(depth);
                let mut state = strat.setup(&smt_problem, depth)?;
                let action = match smt_problem.check() {
                    z3::SatResult::Unsat => {
                        self.extensions.unsat(&mut state, &smt_problem)?;
                        strat.unsat(&mut state, &smt_problem)?
                    }
                    z3::SatResult::Unknown => {
                        self.extensions.unknown(&mut state, &smt_problem)?;
                        strat.unknown(&mut state, &smt_problem)?
                    }
                    z3::SatResult::Sat => {
                        self.extensions.sat(&mut state, &smt_problem)?;
                        strat.sat(&mut state, &smt_problem)?
                    }
                };

                match action {
                    ProofAction::Continue => {
                        self.extensions.finish(&mut self.vmt_model, &mut state)?;
                        strat.finish(state, &mut smt_problem)?;
                    }
                    ProofAction::NextDepth => continue 'bmc,
                    ProofAction::FoundCounterexample => return Err(Error::Counterexample),
                    ProofAction::FoundProof => {
                        return Ok(strat.result(&mut self.vmt_model.clone(), &smt_problem))
                    }
                }
            }
            return Err(Error::TooManyRefinements { n_refines, depth });
        }

        Ok(strat.result(&mut self.vmt_model.clone(), &smt_problem))
    }
}

struct DriverExtensions<'ctx, S> {
    extensions: Vec<Box<dyn ProofStrategyExt<S> + 'ctx>>,
}

impl<S> std::fmt::Debug for DriverExtensions<'_, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[<exts..>]")
    }
}

impl<S> Default for DriverExtensions<'_, S> {
    fn default() -> Self {
        Self { extensions: vec![] }
    }
}

impl<'ctx, S> DriverExtensions<'ctx, S> {
    pub fn add_extension(&mut self, ext: impl ProofStrategyExt<S> + 'ctx) -> &mut Self {
        self.extensions.push(Box::new(ext));
        self
    }
}

impl<S> ProofStrategyExt<S> for DriverExtensions<'_, S> {
    fn unsat(&mut self, state: &mut S, smt: &SMTProblem) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.unsat(state, smt)?;
        }

        Ok(())
    }

    fn sat(&mut self, state: &mut S, smt: &SMTProblem) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.sat(state, smt)?;
        }

        Ok(())
    }

    fn unknown(&mut self, state: &mut S, smt: &SMTProblem) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.unknown(state, smt)?;
        }
        Ok(())
    }

    fn finish(&mut self, model: &mut VMTModel, state: &mut S) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.finish(model, state)?;
        }
        Ok(())
    }
}
