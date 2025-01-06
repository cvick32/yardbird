use log::info;
use smt2parser::vmt::VMTModel;

use crate::{
    strategies::{ProofAction, ProofStrategy, ProofStrategyExt},
    z3_var_context::Z3VarContext,
    YardbirdOptions,
};

#[derive(Debug)]
pub struct ProofLoopResult {
    pub model: Option<VMTModel>,
    pub used_instances: Vec<String>,
    pub const_instances: Vec<String>,
    pub counterexample: bool,
}

#[derive(Debug)]
pub struct Driver<'ctx, S> {
    pub used_instances: Vec<String>,
    pub const_instances: Vec<String>,
    pub vmt_model: VMTModel,
    context: &'ctx z3::Context,
    extensions: DriverExtensions<'ctx, S>,
}

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
        target_depth: u8,
        mut strat: Box<dyn ProofStrategy<'ctx, S>>,
    ) -> anyhow::Result<ProofLoopResult> {
        self.vmt_model = strat.configure_model(self.vmt_model.clone());
        let n_refines = strat.n_refines();

        for depth in 0..target_depth {
            info!("STARTING BMC FOR DEPTH {depth}");
            'refine: for i in 0..n_refines {
                info!("  refining loop: {i}/{n_refines}");

                let smt = self.vmt_model.unroll(depth);
                let solver = z3::Solver::new(&self.context);
                let z3_var_context = Z3VarContext::from(&self.context, &smt);
                solver.from_string(smt.to_bmc());

                let mut state = strat.setup(smt, depth)?;

                let sat_result = solver.check();
                let action = match sat_result {
                    z3::SatResult::Unsat => {
                        self.extensions
                            .unsat(&mut state, &solver, &z3_var_context)?;
                        strat.unsat(&mut state, &solver)?
                    }
                    z3::SatResult::Unknown => {
                        self.extensions.unknown(&mut state, &solver)?;
                        strat.unknown(&mut state, &solver)?
                    }
                    z3::SatResult::Sat => {
                        self.extensions.sat(&mut state, &solver)?;
                        strat.sat(&mut state, &solver, &z3_var_context)?
                    }
                };

                match action {
                    ProofAction::Continue => {
                        self.extensions.finish(&mut self.vmt_model, &mut state)?;
                        strat.finish(&mut self.vmt_model, state)?
                    }
                    ProofAction::NextDepth => break 'refine,
                    ProofAction::Stop => todo!(),
                }
            }
        }

        Ok(strat.result())
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

impl<'ctx, S> ProofStrategyExt<S> for DriverExtensions<'ctx, S> {
    fn unsat(
        &mut self,
        state: &mut S,
        solver: &z3::Solver,
        z3_var_context: &Z3VarContext,
    ) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.unsat(state, solver, z3_var_context)?;
        }

        Ok(())
    }

    fn sat(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.sat(state, solver)?;
        }

        Ok(())
    }

    fn unknown(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.unknown(state, solver)?;
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
