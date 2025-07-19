use log::{debug, info};
use smt2parser::vmt::VMTModel;
use z3::ast::{self, Ast};

use crate::{z3_ext::ModelExt, z3_var_context::Z3VarContext, ProofLoopResult};

use super::{AbstractRefinementState, ProofAction, ProofStrategy};

pub struct Z3NoArrays {
    bmc_depth: u16,
}

impl Z3NoArrays {
    pub fn new(bmc_depth: u16) -> Self {
        Self { bmc_depth }
    }
}

impl ProofStrategy<'_, AbstractRefinementState> for Z3NoArrays {
    fn abstract_array_theory(&self) -> bool {
        true
    }

    fn get_logic_string(&self) -> &'static str {
        "UF"
    }

    fn n_refines(&mut self) -> u32 {
        1
    }

    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        model
            .abstract_array_theory()
            .abstract_constants_over(self.bmc_depth)
    }

    fn customize_solver(&self, ctx: &z3::Context, z3_vars: &Z3VarContext, solver: &mut z3::Solver) {
        let read_fn = z3_vars
            .function_name_to_z3_function
            .get("Read-Int-Int")
            .unwrap();
        let write_fn = z3_vars
            .function_name_to_z3_function
            .get("Write-Int-Int")
            .unwrap();
        let const_fn = z3_vars
            .function_name_to_z3_function
            .get("ConstArr-Int-Int")
            .unwrap();

        let a = ast::Int::new_const(ctx, "a");
        let b = ast::Int::new_const(ctx, "b");
        let const_fn_a = const_fn.apply(&[&a]);
        let read_const_a = read_fn.apply(&[&const_fn_a, &b]);

        // (Read-Int-Int (ConstArr-Int-Int a) b) = a
        let forall: ast::Bool =
            ast::forall_const(ctx, &[&a.clone(), &b], &[], &read_const_a._eq(&a.into()));
        solver.assert(&forall);

        // (Read-Int-Int (Write-Int-Int a idx val) idx) = val
        let a = ast::Dynamic::new_const(
            ctx,
            "a",
            &z3::Sort::uninterpreted(ctx, "Array-Int-Int".into()),
        );
        let idx = ast::Int::new_const(ctx, "idx");
        let val = ast::Int::new_const(ctx, "val");

        let write_expr = write_fn.apply(&[&a, &idx, &val]);
        let lhs = read_fn.apply(&[&write_expr, &idx]);

        let forall: ast::Bool =
            ast::forall_const(ctx, &[&a, &idx, &val.clone()], &[], &lhs._eq(&val.into()));
        solver.assert(&forall);

        // idx != c => (Read-Int-Int (Write-Int-Int a idx val) c) = (Read-Int-Int a c)
        let a = ast::Dynamic::new_const(
            ctx,
            "a",
            &z3::Sort::uninterpreted(ctx, "Array-Int-Int".into()),
        );
        let idx = ast::Int::new_const(ctx, "idx");
        let val = ast::Int::new_const(ctx, "val");
        let c = ast::Int::new_const(ctx, "c");

        let write_expr = write_fn.apply(&[&a, &idx, &val]);
        let lhs_read_expr = read_fn.apply(&[&write_expr, &c]);
        let rhs_read_expr = read_fn.apply(&[&a, &c]);
        let forall = ast::forall_const(
            ctx,
            &[&a, &idx, &val, &c],
            &[],
            &idx._eq(&c)
                .not()
                .implies(&lhs_read_expr._eq(&rhs_read_expr)),
        );
        solver.assert(&forall);
    }

    fn setup(
        &mut self,
        _smt: &crate::smt_problem::SMTProblem,
        depth: u16,
    ) -> crate::driver::Result<AbstractRefinementState> {
        Ok(AbstractRefinementState {
            depth,
            egraph: egg::EGraph::default(),
            instantiations: vec![],
            const_instantiations: vec![],
        })
    }

    fn unsat(
        &mut self,
        _state: &mut AbstractRefinementState,
        _smt: &crate::smt_problem::SMTProblem,
    ) -> crate::driver::Result<super::ProofAction> {
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut AbstractRefinementState,
        smt: &crate::smt_problem::SMTProblem,
    ) -> crate::driver::Result<super::ProofAction> {
        info!("Concrete Counterexample Found at depth: {}!", state.depth);
        let model = match smt.get_model() {
            Some(model) => model,
            None => todo!("No Z3 model available for SAT instance"),
        };
        info!("Counterexample:\n{}", model.dump_sorted()?);
        Ok(ProofAction::FoundCounterexample)
    }

    fn result(
        &mut self,
        model: &mut smt2parser::vmt::VMTModel,
        smt: &crate::smt_problem::SMTProblem,
    ) -> crate::ProofLoopResult {
        ProofLoopResult {
            model: Some(model.clone()),
            used_instances: vec![],
            const_instances: vec![],
            solver_statistics: smt.get_solver_statistics(),
            counterexample: false,
            found_proof: false,
        }
    }
}
