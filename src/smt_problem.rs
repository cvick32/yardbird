use std::{collections::HashSet, vec};

use log::debug;
use smt2parser::{
    concrete::{Command, Term},
    vmt::{
        bmc::BMCBuilder, quantified_instantiator::Instance, smtinterpol_utils, variable::Variable,
        VMTModel,
    },
};

use crate::{
    auxiliary_synthesis::{AuxiliaryRecord, AuxiliarySpec},
    instantiation_strategy::{InstantiationStrategy, StoredInstantiation},
    problem::Problem,
    solver::{new_solver_backend, SolverCheckResult, YardbirdSolver},
    solver_interface::SolverInterface,
    strategies::ProofStrategy,
    subterm_handler::SubtermHandler,
    training::IndexedInstantiationRecord,
    utils::SolverStatistics,
    SolverBackend,
};

pub struct SMTProblem {
    bmc_builder: BMCBuilder,
    sorts: Vec<Command>,
    function_definitions: Vec<Command>,
    variable_definitions: Vec<Command>,
    init_assertion: Term,
    trans_assertion: Term,
    init_and_transition_assertions: Vec<Term>,
    asserted_instantiation_terms: Vec<Term>,
    auxiliary_specs: Vec<AuxiliarySpec>,
    auxiliary_records: Vec<AuxiliaryRecord>,
    auxiliary_transition_assertions: Vec<Term>,
    depth: u16,
    instantiations: Vec<StoredInstantiation>,
    subterm_handler: SubtermHandler,
    pub variables: Vec<Variable>,
    solver: Box<dyn YardbirdSolver>,
    num_quantifiers_instantiated: u64,
    track_instantiations: bool,
    tracked_labels: Vec<crate::training::IndexedInstantiationRecord>,
    instantiation_strategy: Box<dyn InstantiationStrategy>,
}

impl std::fmt::Debug for SMTProblem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SMTProblem")
            .field("depth", &self.depth)
            .field(
                "num_quantifiers_instantiated",
                &self.num_quantifiers_instantiated,
            )
            .field("track_instantiations", &self.track_instantiations)
            .field("variables", &self.variables)
            .finish_non_exhaustive()
    }
}

impl Clone for SMTProblem {
    fn clone(&self) -> Self {
        // SMTProblem contains non-cloneable solver objects and models. Clone is
        // required by the Problem trait but should not be used in practice.
        unimplemented!("SMTProblem::clone() is not implemented")
    }
}

#[allow(clippy::borrowed_box)]
impl SMTProblem {
    pub(crate) fn new<S>(
        vmt_model: &VMTModel,
        strategy: &Box<dyn ProofStrategy<'_, S>>,
        solver_backend: SolverBackend,
        track_instantiations: bool,
        instantiation_strategy: Box<dyn InstantiationStrategy>,
    ) -> Self {
        let current_vars = vmt_model.get_all_current_variable_names();
        let next_to_current_vars = vmt_model.get_next_to_current_varible_names();
        let init_assertion = vmt_model.get_initial_condition_for_yardbird();
        let trans_assertion = vmt_model.get_trans_condition_for_yardbird();
        let solver = new_solver_backend(
            solver_backend,
            &strategy.get_theory_support().get_logic_string(),
        );

        let property_assertion = vmt_model.get_property_for_yardbird();
        let mut smt = SMTProblem {
            sorts: vmt_model.get_sorts(),
            function_definitions: vmt_model.get_function_definitions(),
            variable_definitions: vec![],
            subterm_handler: SubtermHandler::new(
                init_assertion.clone(),
                trans_assertion.clone(),
                property_assertion.clone(),
            ),
            init_assertion,
            trans_assertion,
            init_and_transition_assertions: vec![],
            asserted_instantiation_terms: vec![],
            auxiliary_specs: vec![],
            auxiliary_records: vec![],
            auxiliary_transition_assertions: vec![],
            instantiations: vec![],
            depth: 0,
            bmc_builder: BMCBuilder::new(current_vars, next_to_current_vars),
            variables: vmt_model.get_state_holding_variables(),
            solver,
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
                smt.solver
                    .accept_command(&function_def)
                    .expect("solver should accept VMT function declarations");
            }
        }

        // Add uninterpreted functions declared by the theory
        for func_decl in theory.get_uninterpreted_functions() {
            let command = func_decl.to_command();
            smt.solver
                .accept_command(&command)
                .expect("solver should accept theory function declarations");
            smt.function_definitions.push(command);
        }

        // Add axioms declared by the theory
        for axiom_command in theory.get_axiom_formulas() {
            if let smt2parser::concrete::Command::Assert { term } = axiom_command {
                // Register quantified variables if this is a forall term
                if let smt2parser::concrete::Term::Forall { vars, term: _ } = &term {
                    for (symbol, sort) in vars {
                        smt.solver
                            .create_variable(symbol, sort)
                            .expect("solver should create quantified axiom variables");
                    }
                }
                smt.solver
                    .assert_term(&term)
                    .expect("solver should assert theory axioms");
            }
        }

        // Add initial 0-state variables here, so in the future we only have to add, depth + 1 variables.
        smt.add_solver_variables();
        // Generate initial subterms.
        smt.subterm_handler.generate_subterms(&mut smt.bmc_builder);
        debug!("{:#?}", smt);
        // Add initial assertion.
        smt.add_assertion();
        smt
    }

    /// Adds in all variables at the current depth that is recorded in self.bmc_builder.
    fn add_solver_variables(&mut self) {
        let variables = self.variables.clone();
        for variable in &variables {
            self.add_variable_declaration_at_current_depth(variable);
        }
    }

    fn add_assertion(&mut self) {
        if self.depth == 0 {
            let init = self
                .bmc_builder
                .index_single_step_term(self.init_assertion.clone());
            self.solver
                .assert_term(&init)
                .expect("solver should assert the initial condition");
            self.init_and_transition_assertions.push(init);
        }
        if self.depth != 0 {
            let trans = self
                .bmc_builder
                .index_transition_term(self.trans_assertion.clone());
            self.solver
                .assert_term(&trans)
                .expect("solver should assert the transition condition");
            self.init_and_transition_assertions.push(trans);
            let auxiliary_transitions = self.auxiliary_transition_assertions.clone();
            for transition in auxiliary_transitions {
                let indexed_transition = self.bmc_builder.index_transition_term(transition);
                self.assert_auxiliary_term(indexed_transition);
            }
        }
        // Note: Instantiation handling at each depth is now delegated to
        // the instantiation strategy's on_loop hook, called from unroll()
    }

    fn push_property(&mut self) {
        self.solver.push();
        let prop = self.subterm_handler.get_property_assert();
        self.solver
            .assert_not_term(&prop)
            .expect("solver should assert the negated property");
    }

    pub(crate) fn add_instantiation(
        &mut self,
        inst: Instance,
        abstract_instantiation_id: Option<String>,
    ) -> bool {
        let trace_instantiations = log::log_enabled!(log::Level::Trace);
        let initial_count = self.instantiations.len();
        let inst_text = trace_instantiations.then(|| inst.to_string());
        let abstract_id_for_log = trace_instantiations.then(|| abstract_instantiation_id.clone());

        self.instantiation_strategy.on_generate(
            inst,
            &mut self.instantiations,
            abstract_instantiation_id,
            self.depth,
            &mut self.bmc_builder,
            self.solver.as_mut(),
            &mut self.subterm_handler,
            self.track_instantiations,
            &mut self.tracked_labels,
            &mut self.asserted_instantiation_terms,
            &mut self.num_quantifiers_instantiated,
        );

        // Return true if a new instantiation was added
        let added = self.instantiations.len() > initial_count;
        if trace_instantiations {
            log::trace!(
                "[yardbird::inst-trace] solver-add abstract-id={abstract_instantiation_id:?} added={added} before={before} after={after} term={term}",
                before = initial_count,
                after = self.instantiations.len(),
                term = inst_text.unwrap_or_default(),
                abstract_instantiation_id = abstract_id_for_log.unwrap_or_default(),
            );
        }
        added
    }
    pub(crate) fn to_smtinterpol(&self) -> String {
        let sort_names = unique_command_lines(&self.sorts);
        let function_definitions = unique_command_lines(&self.function_definitions);
        let variable_definitions = unique_command_lines(&self.variable_definitions);

        let mut assertion_index = 0;
        let init_and_trans_asserts = self
            .init_and_transition_assertions
            .iter()
            .map(|assertion| {
                let named = smtinterpol_utils::assert_term_interpolant(assertion_index, assertion);
                assertion_index += 1;
                named
            })
            .collect::<Vec<String>>()
            .join("\n");
        let instantiation_asserts = self
            .asserted_instantiation_terms
            .iter()
            .map(|assertion| {
                let named = smtinterpol_utils::assert_term_interpolant(assertion_index, assertion);
                assertion_index += 1;
                named
            })
            .collect::<Vec<String>>()
            .join("\n");
        let property_assert = smtinterpol_utils::assert_negation_interpolant(
            assertion_index,
            &self.subterm_handler.get_property_assert(),
        );
        let interpolant_command = smtinterpol_utils::get_interpolant_command(assertion_index);

        format!(
            "{options}\n{sort_names}\n{function_definitions}\n{variable_definitions}\n{init_and_trans_asserts}\n{instantiation_asserts}\n{property_assert}\n{interpolant_command}",
            options = smtinterpol_utils::SMT_INTERPOL_OPTIONS
        )
    }

    pub(crate) fn get_number_instantiations_added(&self) -> u64 {
        self.num_quantifiers_instantiated
    }

    pub(crate) fn install_auxiliary_specs(
        &mut self,
        specs: Vec<AuxiliarySpec>,
    ) -> anyhow::Result<()> {
        for spec in specs {
            if self
                .auxiliary_specs
                .iter()
                .any(|existing| existing.aux_id == spec.aux_id)
            {
                continue;
            }

            for variable in spec.variables() {
                self.install_auxiliary_variable(variable);
            }

            for init_term in spec.init_terms() {
                self.assert_auxiliary_init_at_depth_zero(init_term);
            }

            for transition in spec.transition_terms() {
                self.auxiliary_transition_assertions
                    .push(transition.clone());
                for depth in 1..=self.depth {
                    self.assert_auxiliary_transition_at_depth(transition.clone(), depth);
                }
            }

            if let Some(localized_axiom) = &spec.localized_axiom {
                self.assert_auxiliary_localized_axiom(&spec, localized_axiom.clone());
            }

            self.auxiliary_records.push(spec.record(self.depth));
            self.auxiliary_specs.push(spec);
        }
        Ok(())
    }

    pub(crate) fn get_auxiliary_records(&self) -> &[AuxiliaryRecord] {
        &self.auxiliary_records
    }

    /// Dump the solver state to an SMT2 file
    pub(crate) fn dump_solver_to_file(&self, path: &str) -> anyhow::Result<()> {
        use std::fs::File;
        use std::io::Write;

        let smt2_string = self.solver.to_smt2_string()?;
        let mut file = File::create(path)?;
        file.write_all(smt2_string.as_bytes())?;
        Ok(())
    }

    /// Get the unsat core when tracking is enabled
    pub(crate) fn get_unsat_core(&self) -> Option<Vec<String>> {
        if !self.track_instantiations {
            return None;
        }

        self.solver.get_unsat_core().ok()
    }

    /// Get the tracked labels for unsat core analysis
    pub(crate) fn get_tracked_labels(&self) -> &[IndexedInstantiationRecord] {
        &self.tracked_labels
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
            .map(|record| TrackedInst {
                label: record.label.clone(),
                term: record.term.clone(),
                in_core: core_set.contains(&record.label),
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

fn unique_command_lines(commands: &[Command]) -> String {
    let mut seen = HashSet::new();
    commands
        .iter()
        .map(ToString::to_string)
        .filter(|command| seen.insert(command.clone()))
        .collect::<Vec<String>>()
        .join("\n")
}

impl SMTProblem {
    fn add_variable_declaration_at_current_depth(&mut self, variable: &Variable) {
        let bmc_variable = variable
            .current
            .clone()
            .accept(&mut self.bmc_builder)
            .unwrap();
        self.solver
            .accept_command(&bmc_variable)
            .expect("solver should accept BMC variable declarations");
        self.variable_definitions.push(bmc_variable);
    }

    fn install_auxiliary_variable(&mut self, variable: Variable) {
        let current_name = variable.get_current_variable_name().clone();
        let next_name = variable.get_next_variable_name().clone();
        if !self.bmc_builder.current_variables.contains(&current_name) {
            self.bmc_builder
                .current_variables
                .push(current_name.clone());
        }
        self.bmc_builder
            .next_variables
            .insert(next_name, current_name);

        let current_depth = self.bmc_builder.depth;
        for depth in 0..=self.depth {
            self.bmc_builder.set_depth(depth);
            self.add_variable_declaration_at_current_depth(&variable);
        }
        self.bmc_builder.set_depth(current_depth);
        self.variables.push(variable);
    }

    fn assert_auxiliary_transition_at_depth(&mut self, transition: Term, depth: u16) {
        let current_depth = self.bmc_builder.depth;
        self.bmc_builder.set_depth(depth);
        let indexed_transition = self.bmc_builder.index_transition_term(transition);
        self.assert_auxiliary_term(indexed_transition);
        self.bmc_builder.set_depth(current_depth);
    }

    fn assert_auxiliary_init_at_depth_zero(&mut self, init_term: Term) {
        let current_depth = self.bmc_builder.depth;
        self.bmc_builder.set_depth(0);
        let indexed_init = self.bmc_builder.index_single_step_term(init_term);
        self.assert_auxiliary_term(indexed_init);
        self.bmc_builder.set_depth(current_depth);
    }

    fn assert_auxiliary_term(&mut self, term: Term) {
        self.solver
            .assert_term(&term)
            .expect("solver should assert auxiliary terms");
        self.subterm_handler
            .register_instantiation_term(term.clone());
        self.init_and_transition_assertions.push(term);
    }

    fn assert_auxiliary_localized_axiom(&mut self, spec: &AuxiliarySpec, localized_axiom: Term) {
        let current_depth = self.bmc_builder.depth;
        let target_depth = spec
            .non_monotonicity_check
            .source_frame_span
            .max_frame
            .and_then(|frame| u16::try_from(frame).ok())
            .filter(|frame| *frame <= self.depth)
            .unwrap_or(self.depth);
        self.bmc_builder.set_depth(target_depth);
        let indexed_axiom = self.bmc_builder.index_single_step_term(localized_axiom);
        self.assert_auxiliary_term(indexed_axiom);
        self.bmc_builder.set_depth(current_depth);
        log::info!(
            "AUX-SYNTH localized axiom aux_id={} asserted_at_depth={target_depth}",
            spec.aux_id
        );
    }
}

impl Problem for SMTProblem {
    fn get_sorts(&self) -> Vec<smt2parser::concrete::Command> {
        todo!()
    }

    fn get_function_definitions(&self) -> Vec<smt2parser::concrete::Command> {
        todo!()
    }

    fn get_logic(&self) -> Option<String> {
        todo!()
    }

    fn requires_unrolling(&self) -> bool {
        todo!()
    }

    fn as_commands(&self) -> Vec<smt2parser::concrete::Command> {
        todo!()
    }

    /// Checks the satisfiability of BMC `self.bmc_builder.depth`. Handles pushing and popping the property
    /// off of the solver. Keeping the invariant of the property never being on the solver until check
    /// time allows us to not worry about when to add instances and other facts to the solver.
    ///
    /// NOTE: We have to get the model here and set it because once we pop the solver, that model will
    /// be lost.
    fn check(&mut self) -> SolverCheckResult {
        let start_time = std::time::Instant::now();

        // Push property back on top of the solver.
        self.push_property();
        let sat_result = self.solver.check();
        let _ = self.solver.inspect_last_proof();
        if sat_result == SolverCheckResult::Sat {
            let model_terms = self
                .subterm_handler
                .get_all_subterms()
                .into_iter()
                .cloned()
                .collect::<Vec<_>>();
            self.solver
                .preserve_model_values(&model_terms)
                .expect("solver should preserve SAT model values before property pop");
        }
        // Popping property off.
        self.solver.pop(1);
        self.solver.record_statistics_since(start_time);

        sat_result
    }

    fn unroll(&mut self, depth: u16) {
        if depth > self.depth {
            // These things should only happen the first time a new depth is seen.
            // Set new depth.
            self.depth = depth;
            self.bmc_builder.set_depth(self.depth);
            // Generate subterms.
            self.subterm_handler
                .generate_subterms(&mut self.bmc_builder);
            // Add new variables for this depth to the solver backend.
            self.add_solver_variables();
            // Add assertion for current depth.
            self.add_assertion();

            // Call instantiation strategy's on_loop hook to handle instantiations at this depth
            if !self.instantiations.is_empty() {
                let instantiations_snapshot: Vec<StoredInstantiation> = self.instantiations.clone();
                self.instantiation_strategy.on_loop(
                    self.depth,
                    &instantiations_snapshot,
                    &mut self.bmc_builder,
                    self.solver.as_mut(),
                    self.track_instantiations,
                    &mut self.tracked_labels,
                    &mut self.asserted_instantiation_terms,
                    &mut self.num_quantifiers_instantiated,
                );
            }
        }
    }

    fn add_instantiation(&self, _term: &Term) {
        todo!()
    }
}

impl SolverInterface for SMTProblem {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn has_model(&self) -> bool {
        self.solver.has_model()
    }

    fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
        self.solver.eval_to_string(term)
    }

    fn model_to_string(&self) -> anyhow::Result<String> {
        self.solver.model_to_string()
    }

    fn get_all_subterms(&self) -> Vec<&Term> {
        self.subterm_handler.get_all_subterms()
    }

    fn get_solver_statistics(&self) -> SolverStatistics {
        self.solver.get_solver_statistics()
    }

    fn get_reason_unknown(&self) -> Option<String> {
        self.solver.get_reason_unknown()
    }

    fn add_instantiation(
        &mut self,
        inst: Instance,
        abstract_instantiation_id: Option<String>,
    ) -> bool {
        self.add_instantiation(inst, abstract_instantiation_id)
    }

    fn get_instantiations(&self) -> Vec<Term> {
        self.instantiations
            .iter()
            .map(|stored| stored.inst.get_term().clone())
            .collect()
    }

    fn get_variables(&self) -> &[Variable] {
        &self.variables
    }

    fn get_number_instantiations_added(&self) -> u64 {
        self.num_quantifiers_instantiated
    }

    fn get_init_and_transition_subterms(&self) -> Vec<String> {
        let mut trans = self.subterm_handler.get_transition_system_subterms();
        trans.extend(self.subterm_handler.get_initial_subterms());
        trans.extend(self.subterm_handler.get_instantiation_subterms());
        trans
    }

    fn get_property_subterms(&self) -> Vec<String> {
        self.subterm_handler.get_property_subterms()
    }

    fn get_reads_and_writes(&self) -> smt2parser::vmt::ReadsAndWrites {
        self.subterm_handler.get_reads_and_writes()
    }

    fn get_array_types(&self) -> Vec<(String, String)> {
        // For VMT mode, array types are managed by the strategy's discovered_array_types
        // This is a fallback that returns empty - VMT mode uses configure_model instead
        vec![]
    }

    fn install_auxiliary_specs(&mut self, specs: Vec<AuxiliarySpec>) -> anyhow::Result<()> {
        self.install_auxiliary_specs(specs)
    }

    fn get_auxiliary_records(&self) -> Vec<AuxiliaryRecord> {
        self.get_auxiliary_records().to_vec()
    }
}

#[cfg(test)]
mod tests {
    use smt2parser::{
        concrete::{QualIdentifier, Sort, Term},
        vmt::VMTModel,
    };

    use crate::{
        auxiliary_synthesis::{
            AuxiliarySpec, FrameSpan, GuardPolicy, HistorySpec, NonMonotonicityCheckRecord,
            NonMonotonicityStatus, ProphecySpec, SynthesisTrigger,
        },
        cost_functions::array::array_bmc_cost_factory,
        instantiation_strategy::full_unroll::FullUnrollStrategy,
        problem::Problem,
        strategies::{Abstract, ArrayRefinementState, ProofStrategy},
    };

    use super::*;

    #[test]
    fn installs_auxiliary_specs_for_existing_and_future_frames() {
        let model = VMTModel::from_path("./examples/array/array_copy.vmt").unwrap();
        let mut concrete_strategy = Abstract::new(
            4,
            false,
            array_bmc_cost_factory,
            crate::auxiliary_synthesis::AuxSynthesisConfig::default(),
        );
        let model = concrete_strategy.configure_model(model);
        let strategy: Box<dyn ProofStrategy<'_, ArrayRefinementState>> =
            Box::new(concrete_strategy);
        let mut smt = SMTProblem::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            false,
            Box::new(FullUnrollStrategy::new()),
        );

        smt.unroll(1);
        smt.unroll(2);
        let int_sort = Sort::Simple {
            identifier: smt2parser::concrete::Identifier::Simple {
                symbol: smt2parser::concrete::Symbol("Int".to_string()),
            },
        };
        let spec = AuxiliarySpec {
            aux_id: "aux_test".to_string(),
            source_conflict_id: "conflict-test".to_string(),
            source_term_hash: "hash-test".to_string(),
            depth_created: 2,
            refinement_step_created: 0,
            history: HistorySpec {
                name: "yb_hist_test".to_string(),
                next_name: "yb_hist_test_next".to_string(),
                sort: int_sort.clone(),
                capture_term: Term::QualIdentifier(QualIdentifier::simple("i")),
                capture_guard: Term::QualIdentifier(QualIdentifier::simple("true")),
                initial_value: None,
            },
            prophecy: Some(ProphecySpec {
                name: "yb_prop_test".to_string(),
                next_name: "yb_prop_test_next".to_string(),
                sort: int_sort,
                initial_value: None,
            }),
            localized_axiom: Some(
                "(= (Read_Int_Int (Write_Int_Int a@0 i@0 i@0) yb_prop_test) (Read_Int_Int a@0 yb_prop_test))"
                    .parse()
                    .unwrap(),
            ),
            property_constraint: None,
            guard_policy: GuardPolicy::True,
            trigger: SynthesisTrigger::NonLocal,
            non_monotonicity_check: NonMonotonicityCheckRecord {
                status: NonMonotonicityStatus::Pending,
                source_term: "(= i@0 i@2)".to_string(),
                localized_term: Some("(= i@0 yb_prop_test)".to_string()),
                source_frame_span: FrameSpan::from_term(&"(= i@0 i@2)".parse().unwrap()),
                localized_frame_span: Some(FrameSpan::from_term(
                    &"(= i@0 yb_prop_test)".parse().unwrap(),
                )),
                note: "test".to_string(),
            },
        };

        smt.install_auxiliary_specs(vec![spec]).unwrap();
        assert_eq!(smt.get_auxiliary_records().len(), 1);
        assert!(smt.to_smtinterpol().contains("yb_hist_test@2"));
        assert!(smt.to_smtinterpol().contains("yb_prop_test@0"));

        smt.unroll(3);
        let interpolant_problem = smt.to_smtinterpol();
        assert!(interpolant_problem.contains("yb_hist_test@3"));
        assert!(interpolant_problem.contains("yb_prop_test@3"));
    }
}
