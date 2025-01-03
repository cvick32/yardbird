use log::info;
use smt2parser::vmt::VMTModel;

use crate::{
    strategies::{ProofAction, ProofStrategy, ProofStrategyExt},
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
pub struct Driver<'a> {
    pub used_instances: Vec<String>,
    pub const_instances: Vec<String>,
    context: z3::Context,
    pub vmt_model: VMTModel,
    _options: &'a YardbirdOptions,
}

impl<'a> Driver<'a> {
    pub fn new(options: &'a YardbirdOptions, config: &z3::Config, vmt_model: VMTModel) -> Self {
        Self {
            used_instances: vec![],
            const_instances: vec![],
            context: z3::Context::new(config),
            vmt_model,
            _options: options,
        }
    }

    pub fn check_strategy<'ctx, S>(
        &'a mut self,
        target_depth: u8,
        mut strat: Box<dyn ProofStrategy<'ctx, S>>,
        extensions: &mut DriverExtensions<'ctx, S>,
    ) -> anyhow::Result<ProofLoopResult>
    where
        'a: 'ctx,
    {
        self.vmt_model = strat.configure_model(self.vmt_model.clone());
        let n_refines = strat.n_refines();

        for depth in 0..target_depth {
            info!("STARTING BMC FOR DEPTH {depth}");
            'refine: for i in 0..n_refines {
                info!("  refining loop: {i}/{n_refines}");

                let smt = self.vmt_model.unroll(depth);
                let solver = z3::Solver::new(&self.context);
                solver.from_string(smt.to_bmc());

                let mut state = strat.setup(&self.context, smt, depth)?;

                let sat_result = solver.check();
                let action = match sat_result {
                    z3::SatResult::Unsat => {
                        extensions.unsat(&mut state, &solver)?;
                        strat.unsat(&mut state, &solver)?
                    }
                    z3::SatResult::Unknown => {
                        extensions.unknown(&mut state, &solver)?;
                        strat.unknown(&mut state, &solver)?
                    }
                    z3::SatResult::Sat => {
                        extensions.sat(&mut state, &solver)?;
                        strat.sat(&mut state, &solver)?
                    }
                };

                match action {
                    ProofAction::Continue => {
                        extensions.finish(&mut self.vmt_model, &mut state)?;
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

pub struct DriverExtensions<'ctx, S> {
    extensions: Vec<Box<dyn ProofStrategyExt<'ctx, S> + 'ctx>>,
}

impl<S> Default for DriverExtensions<'_, S> {
    fn default() -> Self {
        Self { extensions: vec![] }
    }
}

impl<'ctx, S> DriverExtensions<'ctx, S> {
    pub fn add_extension(&mut self, ext: impl ProofStrategyExt<'ctx, S> + 'ctx) -> &mut Self {
        self.extensions.push(Box::new(ext));
        self
    }
}

impl<'ctx, S> ProofStrategyExt<'ctx, S> for DriverExtensions<'ctx, S> {
    fn unsat(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.unsat(state, solver)?;
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
