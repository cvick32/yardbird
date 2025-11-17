use std::vec;

use log::debug;
use smt2parser::{
    concrete::Term,
    vmt::{bmc::BMCBuilder, quantified_instantiator::Instance, variable::Variable, VMTModel},
};
use z3::ast::Dynamic;

use crate::{
    instantiation_strategy::InstantiationStrategy, proof_tree::ProofTree,
    strategies::ProofStrategy, subterm_handler::SubtermHandler, utils::SolverStatistics,
    z3_var_context::Z3VarContext,
};

pub struct SMTProblem {
    z3_var_context: Z3VarContext,
    bmc_builder: BMCBuilder,
    init_assertion: Term,
    trans_assertion: Term,
    depth: u16,
    instantiations: Vec<Instance>,
    subterm_handler: SubtermHandler,
    pub variables: Vec<Variable>,
    solver: z3::Solver,
    solver_statistcs: SolverStatistics,
    newest_model: Option<z3::Model>,
    num_quantifiers_instantiated: u64,
    track_instantiations: bool,
    tracked_labels: Vec<(String, Term)>, // (label, instantiation_term)
    instantiation_strategy: Box<dyn InstantiationStrategy>,
}

#[allow(clippy::borrowed_box)]
impl SMTProblem {
    pub(crate) fn new<S>(
        vmt_model: &VMTModel,
        strategy: &Box<dyn ProofStrategy<'_, S>>,
        track_instantiations: bool,
        instantiation_strategy: Box<dyn InstantiationStrategy>,
    ) -> Self {
        let current_vars = vmt_model.get_all_current_variable_names();
        let next_to_current_vars = vmt_model.get_next_to_current_varible_names();
        let init_assertion = vmt_model.get_initial_condition_for_yardbird();
        let trans_assertion = vmt_model.get_trans_condition_for_yardbird();
        let solver =
            z3::Solver::new_for_logic(strategy.get_theory_support().get_logic_string()).unwrap();

        let property_assertion = vmt_model.get_property_for_yardbird();
        let mut smt = SMTProblem {
            subterm_handler: SubtermHandler::new(
                init_assertion.clone(),
                trans_assertion.clone(),
                property_assertion.clone(),
            ),
            init_assertion,
            trans_assertion,
            instantiations: vec![],
            depth: 0,
            bmc_builder: BMCBuilder::new(current_vars, next_to_current_vars),
            variables: vmt_model.get_state_holding_variables(),
            solver,
            solver_statistcs: SolverStatistics::new(),
            z3_var_context: Z3VarContext::new(),
            newest_model: None,
            num_quantifiers_instantiated: 0,
            track_instantiations,
            tracked_labels: vec![],
            instantiation_strategy,
        };
        // Handle theory-specific function declarations
        let theory = strategy.get_theory_support();
        if theory.requires_abstraction() {
            // Add in abstracted function definitions from VMT model
            for function_def in vmt_model.get_function_definitions() {
                let _ = function_def.accept(&mut smt.z3_var_context);
            }
        }

        // Add uninterpreted functions declared by the theory
        for func_decl in theory.get_uninterpreted_functions() {
            let command = func_decl.to_command();
            let _ = command.accept(&mut smt.z3_var_context);
        }

        // Add axioms declared by the theory
        for axiom_command in theory.get_axiom_formulas() {
            if let smt2parser::concrete::Command::Assert { term } = axiom_command {
                // Register quantified variables if this is a forall term
                if let smt2parser::concrete::Term::Forall { vars, term: _ } = &term {
                    for (symbol, sort) in vars {
                        smt.z3_var_context.create_variable(symbol, sort);
                    }
                }
                let z3_axiom = smt.z3_var_context.rewrite_term(&term);
                smt.solver.assert(z3_axiom.as_bool().unwrap());
            }
        }

        // Add initial 0-state variables here, so in the future we only have to add, depth + 1 variables.
        for variable in &smt.variables {
            let bmc_variable = variable
                .current
                .clone()
                .accept(&mut smt.bmc_builder)
                .unwrap();
            let _ = bmc_variable.accept(&mut smt.z3_var_context);
        }
        // Generate initial subterms.
        smt.subterm_handler.generate_subterms(&mut smt.bmc_builder);
        // Add initial assertion.
        smt.add_assertion();
        smt
    }

    /// Adds in all variables at the current depth that is recorded in self.bmc_builder.
    fn add_z3_variables(&mut self) {
        for variable in &self.variables {
            let bmc_variable = variable
                .current
                .clone()
                .accept(&mut self.bmc_builder)
                .unwrap();
            let _ = bmc_variable.accept(&mut self.z3_var_context);
        }
    }

    pub fn get_model(&self) -> &Option<z3::Model> {
        &self.newest_model
    }

    fn add_assertion(&mut self) {
        if self.depth == 0 {
            let init = self
                .bmc_builder
                .index_single_step_term(self.init_assertion.clone());
            let z3_init = self.z3_var_context.rewrite_term(&init);
            self.solver.assert(z3_init.as_bool().unwrap());
        }
        if self.depth != 0 {
            let trans = self
                .bmc_builder
                .index_transition_term(self.trans_assertion.clone());
            let z3_trans = self.z3_var_context.rewrite_term(&trans);
            self.solver.assert(z3_trans.as_bool().unwrap());
        }
        // Note: Instantiation handling at each depth is now delegated to
        // the instantiation strategy's on_loop hook, called from unroll()
    }

    // All instantiations have been added self.current_depth number of times when
    // this function is called. We only need to unroll transition and all instantiations
    // one more time.
    pub(crate) fn unroll(&mut self, depth: u16) {
        if depth > self.depth {
            // These things should only happen the first time a new depth is seen.
            // Set new depth.
            self.depth = depth;
            self.bmc_builder.set_depth(self.depth);
            // Generate subterms.
            self.subterm_handler
                .generate_subterms(&mut self.bmc_builder);
            // Add new variables to Z3VarContext for depth.
            self.add_z3_variables();
            // Add assertion for current depth.
            self.add_assertion();

            // Call instantiation strategy's on_loop hook to handle instantiations at this depth
            if !self.instantiations.is_empty() {
                let instantiations_snapshot: Vec<Instance> = self.instantiations.clone();
                self.instantiation_strategy.on_loop(
                    self.depth,
                    &instantiations_snapshot,
                    &mut self.bmc_builder,
                    &mut self.z3_var_context,
                    &mut self.solver,
                    self.track_instantiations,
                    &mut self.tracked_labels,
                    &mut self.num_quantifiers_instantiated,
                );
            }
        }
    }

    /// Checks the satisfiability of BMC `self.bmc_builder.depth`. Handles pushing and popping the property
    /// off of the solver. Keeping the invariant of the property never being on the solver until check
    /// time allows us to not worry about when to add instances and other facts to the solver.
    ///
    /// NOTE: We have to get the model here and set it because once we pop the solver, that model will
    /// be lost.
    pub(crate) fn check(&mut self) -> z3::SatResult {
        let start_time = std::time::Instant::now();

        // Push property back on top of the solver.
        self.push_property();
        //println!("solver: {:#?}", self.solver);
        let sat_result = self.solver.check();
        self.newest_model = self.solver.get_model();
        match self.solver.get_proof() {
            Some(proof) => {
                ProofTree::new(proof);
            }
            None => debug!("NO PROOF!"),
        }
        // Popping property off.
        self.solver.pop(1);
        self.solver_statistcs
            .join_from_z3_statistics(self.solver.get_statistics());

        // Track total check time
        let check_duration = start_time.elapsed();
        self.solver_statistcs
            .add_time("solver_time", check_duration.as_secs_f64());

        sat_result
    }

    fn push_property(&mut self) {
        self.solver.push();
        let prop = self.subterm_handler.get_property_assert();
        let z3_prop_negated =
            z3::ast::Bool::not(&self.z3_var_context.rewrite_term(&prop).as_bool().unwrap());
        self.solver.assert(&z3_prop_negated);
    }

    pub(crate) fn add_instantiation(&mut self, inst: Instance) -> bool {
        let initial_count = self.instantiations.len();

        self.instantiation_strategy.on_generate(
            inst,
            &mut self.instantiations,
            self.depth,
            &mut self.bmc_builder,
            &mut self.z3_var_context,
            &mut self.solver,
            &mut self.subterm_handler,
            self.track_instantiations,
            &mut self.tracked_labels,
            &mut self.num_quantifiers_instantiated,
        );

        // Return true if a new instantiation was added
        self.instantiations.len() > initial_count
    }

    pub(crate) fn get_solver_statistics(&self) -> SolverStatistics {
        self.solver_statistcs.clone()
    }

    pub(crate) fn get_reason_unknown(&self) -> Option<String> {
        self.solver.get_reason_unknown()
    }

    pub(crate) fn rewrite_term(&self, term: &Term) -> Dynamic {
        self.z3_var_context.rewrite_term(term)
    }

    pub(crate) fn get_property_subterms(&self) -> Vec<String> {
        self.subterm_handler.get_property_subterms()
    }

    pub(crate) fn get_reads_and_writes(&self) -> smt2parser::vmt::ReadsAndWrites {
        self.subterm_handler.get_reads_and_writes()
    }

    pub(crate) fn get_all_subterms(&self) -> Vec<&Term> {
        self.subterm_handler.get_all_subterms()
    }

    pub(crate) fn to_smtinterpol(&self) -> String {
        todo!()
    }

    pub(crate) fn get_instantiations(&self) -> Vec<Term> {
        self.instantiations
            .iter()
            .map(|inst| inst.get_term().clone())
            .collect()
    }

    pub(crate) fn get_number_instantiations_added(&self) -> u64 {
        self.num_quantifiers_instantiated
    }

    pub(crate) fn get_init_and_transition_subterms(&self) -> Vec<String> {
        let mut trans = self.subterm_handler.get_transition_system_subterms();
        trans.extend(self.subterm_handler.get_initial_subterms());
        trans.extend(self.subterm_handler.get_instantiation_subterms());
        trans
    }

    pub(crate) fn get_interpretation(&self, model: &z3::Model, z3_term: &Dynamic) -> Dynamic {
        self.z3_var_context.get_interpretation(model, z3_term)
    }

    /// Dump the solver state to an SMT2 file
    pub(crate) fn dump_solver_to_file(&self, path: &str) -> anyhow::Result<()> {
        use std::fs::File;
        use std::io::Write;

        let smt2_string = self.solver.to_string();
        let mut file = File::create(path)?;
        file.write_all(smt2_string.as_bytes())?;
        Ok(())
    }

    /// Get the unsat core when tracking is enabled
    pub(crate) fn get_unsat_core(&self) -> Option<Vec<String>> {
        if !self.track_instantiations {
            return None;
        }

        let core_asts = self.solver.get_unsat_core();
        let core_labels: Vec<String> = core_asts.iter().map(|ast| ast.to_string()).collect();

        Some(core_labels)
    }

    /// Export unsat core analysis to JSON
    pub(crate) fn export_unsat_core_json(&self, path: &str) -> anyhow::Result<()> {
        use std::fs::File;
        use std::io::Write;

        if !self.track_instantiations {
            anyhow::bail!("Tracking is not enabled, cannot export unsat core");
        }

        let core_labels = self
            .get_unsat_core()
            .ok_or_else(|| anyhow::anyhow!("Failed to get unsat core"))?;

        #[derive(serde::Serialize)]
        struct UnsatCoreData {
            total_instantiations: usize,
            core_size: usize,
            core_labels: Vec<String>,
            tracked_instantiations: Vec<TrackedInst>,
            core_instantiations: Vec<TrackedInst>,
        }

        #[derive(serde::Serialize, Clone)]
        struct TrackedInst {
            label: String,
            term: String,
            in_core: bool,
        }

        let core_set: std::collections::HashSet<_> = core_labels.iter().collect();

        let tracked_instantiations: Vec<TrackedInst> = self
            .tracked_labels
            .iter()
            .map(|(label, term)| TrackedInst {
                label: label.clone(),
                term: term.to_string(),
                in_core: core_set.contains(label),
            })
            .collect();

        let core_instantiations: Vec<TrackedInst> = tracked_instantiations
            .iter()
            .filter(|inst| inst.in_core)
            .cloned()
            .collect();

        let data = UnsatCoreData {
            total_instantiations: self.tracked_labels.len(),
            core_size: core_labels.len(),
            core_labels,
            tracked_instantiations,
            core_instantiations,
        };

        let json = serde_json::to_string_pretty(&data)?;
        let mut file = File::create(path)?;
        file.write_all(json.as_bytes())?;

        Ok(())
    }
}
