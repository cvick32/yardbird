use std::{
    collections::{BTreeMap, HashSet},
    time::Instant,
    vec,
};

use log::debug;
use smt2parser::{
    concrete::{Command, Term},
    vmt::{
        bmc::BMCBuilder,
        definition_graph::DefinitionFrameInfo,
        definition_materializer::{DefinitionMaterializer, MaterializedTerm},
        quantified_instantiator::Instance,
        smtinterpol_utils,
        variable::Variable,
        VMTModel,
    },
};

use crate::{
    auxiliary_synthesis::{AuxiliaryRecord, AuxiliarySpec},
    instantiation_strategy::{InstantiationStrategy, StoredInstantiation},
    problem_context::ProblemContext,
    profiling::{SolverCheckMeasurement, SolverProfileMetadata},
    solver::{
        check::{run_solver_check, SolverCheckRequest},
        new_solver_backend, SolverCapture, SolverCheckResult, YardbirdSolver,
    },
    strategies::ProofStrategy,
    subterm_handler::SubtermHandler,
    training::IndexedInstantiationRecord,
    utils::SolverStatistics,
    SolverBackend,
};

const DUMP_PROPERTY_LABEL: &str = "yardbird_negated_property";

#[derive(Clone, Debug)]
struct NamedAssertion {
    label: String,
    term: Term,
}

impl NamedAssertion {
    fn new(label: impl Into<String>, term: Term) -> Self {
        Self {
            label: label.into(),
            term,
        }
    }
}

pub struct VmtBmcSession {
    bmc_builder: BMCBuilder,
    definition_materializer: DefinitionMaterializer,
    sorts: Vec<Command>,
    function_definitions: Vec<Command>,
    variable_definitions: Vec<Command>,
    input_variables: Vec<Command>,
    init_assertion: Term,
    trans_assertion: Term,
    property_assertion: Term,
    init_and_transition_assertions: Vec<NamedAssertion>,
    theory_axiom_assertions: Vec<Term>,
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
    logic: String,
    collect_check_profiles: bool,
    last_solver_check_profile: Option<SolverCheckMeasurement>,
    last_check_profile: BTreeMap<String, f64>,
    last_unroll_profile: BTreeMap<String, f64>,
}

impl std::fmt::Debug for VmtBmcSession {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VmtBmcSession")
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

impl Clone for VmtBmcSession {
    fn clone(&self) -> Self {
        // VmtBmcSession contains non-cloneable solver objects and models.
        unimplemented!("VmtBmcSession::clone() is not implemented")
    }
}

fn format_smt2_with_property_check(base_smt2: &str, property_assert: &Term) -> String {
    let mut output = String::from("(set-option :produce-unsat-cores true)\n");
    output.push_str(base_smt2);
    if !base_smt2.ends_with('\n') {
        output.push('\n');
    }
    output.push_str(&format!(
        "(assert (! (not {property_assert}) :named {DUMP_PROPERTY_LABEL}))\n\
         (check-sat)\n\
         (get-unsat-core)\n"
    ));
    output
}

fn nanos_to_secs(nanos: u64) -> f64 {
    nanos as f64 / 1_000_000_000.0
}

fn format_assertions(terms: &[Term]) -> String {
    terms
        .iter()
        .map(|term| format!("(assert {term})"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn format_named_assertions(assertions: &[NamedAssertion]) -> String {
    assertions
        .iter()
        .map(|assertion| format!("(assert (! {} :named {}))", assertion.term, assertion.label))
        .collect::<Vec<_>>()
        .join("\n")
}

#[allow(clippy::borrowed_box)]
impl VmtBmcSession {
    pub(crate) fn new<S>(
        vmt_model: &VMTModel,
        strategy: &Box<dyn ProofStrategy<'_, S>>,
        solver_backend: SolverBackend,
        track_instantiations: bool,
        instantiation_strategy: Box<dyn InstantiationStrategy>,
        collect_check_profiles: bool,
        solver_capture: Option<SolverCapture>,
    ) -> Self {
        let current_vars = vmt_model.get_all_current_variable_names();
        let next_to_current_vars = vmt_model.get_next_to_current_varible_names();
        let helper_definitions = vmt_model.get_helper_definitions().clone();
        let definition_frames =
            DefinitionFrameInfo::new(&helper_definitions, &current_vars, &next_to_current_vars);
        let init_assertion = vmt_model.get_initial_condition_for_yardbird();
        let trans_assertion = vmt_model.get_trans_condition_for_yardbird();
        let property_assertion = vmt_model.get_property_for_yardbird();
        let theory = strategy.get_theory_support();
        let logic = theory.get_logic_string_for_terms(&[
            &init_assertion,
            &trans_assertion,
            &property_assertion,
        ]);
        let solver = new_solver_backend(solver_backend, &logic, solver_capture);

        let mut smt = VmtBmcSession {
            sorts: vmt_model.get_sorts(),
            function_definitions: vmt_model.get_function_definitions(),
            variable_definitions: vec![],
            input_variables: vmt_model.get_input_variables(),
            subterm_handler: SubtermHandler::new(
                init_assertion.clone(),
                trans_assertion.clone(),
                property_assertion.clone(),
            ),
            init_assertion,
            trans_assertion,
            property_assertion,
            init_and_transition_assertions: vec![],
            theory_axiom_assertions: vec![],
            asserted_instantiation_terms: vec![],
            auxiliary_specs: vec![],
            auxiliary_records: vec![],
            auxiliary_transition_assertions: vec![],
            instantiations: vec![],
            depth: 0,
            bmc_builder: BMCBuilder::with_definition_frames(
                current_vars,
                next_to_current_vars,
                definition_frames.clone(),
            ),
            definition_materializer: DefinitionMaterializer::new(
                helper_definitions,
                definition_frames,
            ),
            variables: vmt_model.get_state_variables(),
            solver,
            num_quantifiers_instantiated: 0,
            track_instantiations,
            tracked_labels: vec![],
            instantiation_strategy,
            logic,
            collect_check_profiles,
            last_solver_check_profile: None,
            last_check_profile: BTreeMap::new(),
            last_unroll_profile: BTreeMap::new(),
        };
        let mut accepted_declarations = HashSet::new();
        for sort in vmt_model.get_sorts() {
            if accepted_declarations.insert(sort.clone()) {
                smt.solver
                    .accept_command(&sort)
                    .expect("solver should accept VMT sort declarations");
            }
        }

        // Handle theory-specific function declarations
        if theory.requires_abstraction() {
            // Add in abstracted function definitions from VMT model
            for function_def in vmt_model.get_function_definitions() {
                if accepted_declarations.insert(function_def.clone()) {
                    smt.solver
                        .accept_command(&function_def)
                        .expect("solver should accept VMT function declarations");
                }
            }
        }

        // Add uninterpreted functions declared by the theory
        for func_decl in theory.get_uninterpreted_functions() {
            let command = func_decl.to_command();
            if accepted_declarations.insert(command.clone()) {
                smt.solver
                    .accept_command(&command)
                    .expect("solver should accept theory function declarations");
            }
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
                smt.theory_axiom_assertions.push(term);
            }
        }

        // Add initial 0-state variables here, so in the future we only have to add, depth + 1 variables.
        smt.add_solver_variables();
        smt.subterm_handler.generate_subterms(&mut smt.bmc_builder);
        smt.add_initial_assertion();
        smt.update_property();
        debug!("{:#?}", smt);
        smt
    }

    /// Adds in all variables at the current depth that is recorded in self.bmc_builder.
    fn add_solver_variables(&mut self) {
        let variables = self.variables.clone();
        for variable in &variables {
            self.add_variable_declaration_at_current_depth(variable);
        }
        let input_variables = self.input_variables.clone();
        for input in &input_variables {
            self.add_declaration_at_current_depth(input);
        }
    }

    fn add_initial_assertion(&mut self) {
        let init = self
            .bmc_builder
            .index_single_step_term(self.init_assertion.clone());
        let materialized = self.materialize(init);
        self.subterm_handler
            .register_initial_support(&materialized.support);
        self.install_materialized_support(&materialized);
        self.solver
            .assert_term(&materialized.root)
            .expect("solver should assert the initial condition");
        self.init_and_transition_assertions
            .push(NamedAssertion::new("yardbird_init_0", materialized.root));
    }

    fn add_transition_assertion(&mut self) {
        let trans = self
            .bmc_builder
            .index_transition_term(self.trans_assertion.clone());
        let materialized = self.materialize(trans);
        self.subterm_handler
            .register_transition_support(&materialized.support);
        self.install_materialized_support(&materialized);
        self.solver
            .assert_term(&materialized.root)
            .expect("solver should assert the transition condition");
        self.init_and_transition_assertions
            .push(NamedAssertion::new(
                format!("yardbird_trans_{}_to_{}", self.depth - 1, self.depth),
                materialized.root,
            ));

        let auxiliary_transitions = self.auxiliary_transition_assertions.clone();
        for (index, transition) in auxiliary_transitions.into_iter().enumerate() {
            let indexed_transition = self.bmc_builder.index_transition_term(transition);
            self.assert_auxiliary_term(
                indexed_transition,
                format!(
                    "yardbird_aux_trans_{}_to_{}_{}",
                    self.depth - 1,
                    self.depth,
                    index
                ),
            );
        }
    }

    fn update_property(&mut self) {
        let property = self
            .bmc_builder
            .index_single_step_term(self.property_assertion.clone());
        let materialized = self.materialize(property);
        self.subterm_handler
            .register_property_support(&materialized.support);
        self.install_materialized_support(&materialized);
    }

    fn materialize(&mut self, term: Term) -> MaterializedTerm {
        self.definition_materializer
            .materialize(term, &mut self.bmc_builder)
    }

    fn install_materialized_support(&mut self, materialized: &MaterializedTerm) {
        for declaration in &materialized.new_declarations {
            self.solver
                .accept_command(declaration)
                .expect("solver should accept a materialized helper declaration");
        }
        for definition in &materialized.new_definitions {
            self.solver
                .assert_term(definition)
                .expect("solver should assert a materialized helper definition");
        }
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
            &mut self.definition_materializer,
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
        let helper_declarations =
            unique_command_lines(&self.definition_materializer.declarations());

        let mut assertion_index = 0;
        let helper_definition_asserts = self
            .definition_materializer
            .definitions()
            .iter()
            .map(|assertion| {
                let named = smtinterpol_utils::assert_term_interpolant(assertion_index, assertion);
                assertion_index += 1;
                named
            })
            .collect::<Vec<String>>()
            .join("\n");
        let init_and_trans_asserts = self
            .init_and_transition_assertions
            .iter()
            .map(|assertion| {
                let named =
                    smtinterpol_utils::assert_term_interpolant(assertion_index, &assertion.term);
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
            "{options}\n{sort_names}\n{function_definitions}\n{variable_definitions}\n{helper_declarations}\n{helper_definition_asserts}\n{init_and_trans_asserts}\n{instantiation_asserts}\n{property_assert}\n{interpolant_command}",
            options = smtinterpol_utils::SMT_INTERPOL_OPTIONS
        )
    }

    pub(crate) fn get_number_instantiations_added(&self) -> u64 {
        self.num_quantifiers_instantiated
    }

    pub(crate) fn take_last_check_profile(&mut self) -> BTreeMap<String, f64> {
        std::mem::take(&mut self.last_check_profile)
    }

    pub(crate) fn take_last_solver_check_profile(&mut self) -> Option<SolverCheckMeasurement> {
        self.last_solver_check_profile.take()
    }

    pub(crate) fn solver_profile_metadata(&self) -> SolverProfileMetadata {
        SolverProfileMetadata {
            backend: self.solver.backend(),
            logic: self.logic.clone(),
            parameters: self.solver.solver_parameters(),
            random_seeds: self.solver.random_seeds(),
        }
    }

    pub(crate) fn take_last_unroll_profile(&mut self) -> BTreeMap<String, f64> {
        std::mem::take(&mut self.last_unroll_profile)
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

    /// Dump the solver state to an SMT2 file that can be replayed from the
    /// command line to reproduce the last property check and print its core.
    pub(crate) fn dump_solver_to_file(&self, path: &str) -> anyhow::Result<()> {
        use std::fs::File;
        use std::io::Write;

        let smt2_string = self.smt2_string_with_property_check();
        let mut file = File::create(path)?;
        file.write_all(smt2_string.as_bytes())?;
        Ok(())
    }

    fn smt2_string_with_property_check(&self) -> String {
        let mut sections = vec![
            unique_command_lines(&self.sorts),
            unique_command_lines(&self.function_definitions),
            unique_command_lines(&self.variable_definitions),
            unique_command_lines(&self.definition_materializer.declarations()),
            format_assertions(&self.theory_axiom_assertions),
            format_assertions(&self.definition_materializer.definitions()),
            format_named_assertions(&self.init_and_transition_assertions),
            self.format_instantiation_assertions(),
        ];
        sections.retain(|section| !section.is_empty());
        let base_smt2 = sections.join("\n");
        format_smt2_with_property_check(&base_smt2, &self.subterm_handler.get_property_assert())
    }

    fn format_instantiation_assertions(&self) -> String {
        if self.track_instantiations {
            self.tracked_labels
                .iter()
                .map(|record| format!("(assert (! {} :named {}))", record.term, record.label))
                .collect::<Vec<_>>()
                .join("\n")
        } else {
            format_assertions(&self.asserted_instantiation_terms)
        }
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

impl VmtBmcSession {
    fn add_variable_declaration_at_current_depth(&mut self, variable: &Variable) {
        self.add_declaration_at_current_depth(&variable.current);
    }

    fn add_declaration_at_current_depth(&mut self, declaration: &Command) {
        let bmc_variable = declaration.clone().accept(&mut self.bmc_builder).unwrap();
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
        let label = format!(
            "yardbird_aux_trans_{}_to_{}_{}",
            depth - 1,
            depth,
            self.init_and_transition_assertions.len()
        );
        self.assert_auxiliary_term(indexed_transition, label);
        self.bmc_builder.set_depth(current_depth);
    }

    fn assert_auxiliary_init_at_depth_zero(&mut self, init_term: Term) {
        let current_depth = self.bmc_builder.depth;
        self.bmc_builder.set_depth(0);
        let indexed_init = self.bmc_builder.index_single_step_term(init_term);
        let label = format!(
            "yardbird_aux_init_0_{}",
            self.init_and_transition_assertions.len()
        );
        self.assert_auxiliary_term(indexed_init, label);
        self.bmc_builder.set_depth(current_depth);
    }

    fn assert_auxiliary_term(&mut self, term: Term, label: impl Into<String>) {
        let materialized = self.materialize(term);
        self.install_materialized_support(&materialized);
        self.solver
            .assert_term(&materialized.root)
            .expect("solver should assert auxiliary terms");
        self.subterm_handler
            .register_instantiation_term(materialized.root.clone());
        for support in &materialized.support {
            self.subterm_handler
                .register_instantiation_term(support.clone());
        }
        self.init_and_transition_assertions
            .push(NamedAssertion::new(label, materialized.root));
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
        let label = format!(
            "yardbird_aux_localized_{}_{}",
            self.auxiliary_records.len(),
            target_depth
        );
        self.assert_auxiliary_term(indexed_axiom, label);
        self.bmc_builder.set_depth(current_depth);
        log::info!(
            "AUX-SYNTH localized axiom aux_id={} asserted_at_depth={target_depth}",
            spec.aux_id
        );
    }
}

impl VmtBmcSession {
    /// Checks the satisfiability of BMC `self.bmc_builder.depth`. Handles pushing and popping the property
    /// off of the solver. Keeping the invariant of the property never being on the solver until check
    /// time allows us to not worry about when to add instances and other facts to the solver.
    ///
    /// NOTE: We have to get the model here and set it because once we pop the solver, that model will
    /// be lost.
    pub(crate) fn check_property(&mut self) -> SolverCheckResult {
        self.last_check_profile.clear();
        self.last_solver_check_profile = None;
        let assertion_count = (self.theory_axiom_assertions.len()
            + self.init_and_transition_assertions.len()
            + self.asserted_instantiation_terms.len()
            + 1) as u64;
        let property = self.subterm_handler.get_property_assert();
        let model_terms = self
            .subterm_handler
            .get_all_subterms()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        let outcome = run_solver_check(
            self.solver.as_mut(),
            SolverCheckRequest {
                profiling_enabled: self.collect_check_profiles,
                assertion_count,
                temporary_negated_property: Some(&property),
                model_terms: Some(&model_terms),
                capture_unsat_core: self.track_instantiations,
            },
        );

        if let Some(measurement) = outcome.measurement {
            let timing = &measurement.timing_ns;
            self.last_check_profile.insert(
                "check_push_property".to_string(),
                nanos_to_secs(timing.property_push),
            );
            self.last_check_profile
                .insert("check_solver".to_string(), nanos_to_secs(timing.raw_check));
            self.last_check_profile.insert(
                "check_capture_model".to_string(),
                nanos_to_secs(timing.model_acquisition),
            );
            self.last_check_profile.insert(
                "check_proof_core_access".to_string(),
                nanos_to_secs(timing.proof_core_access),
            );
            self.last_check_profile
                .insert("check_pop".to_string(), nanos_to_secs(timing.property_pop));
            self.last_check_profile.insert(
                "check_record_statistics".to_string(),
                nanos_to_secs(timing.statistics_collection),
            );
            self.last_check_profile.insert(
                "check_total".to_string(),
                nanos_to_secs(timing.total_check_handling),
            );
            self.last_solver_check_profile = Some(measurement);
        }

        self.solver.complete_check();
        outcome.result
    }

    pub(crate) fn unroll(&mut self, depth: u16) {
        self.last_unroll_profile.clear();
        let unroll_start = Instant::now();
        if depth > self.depth {
            // These things should only happen the first time a new depth is seen.
            // Set new depth.
            self.depth = depth;
            self.bmc_builder.set_depth(self.depth);
            // Preserve the established subterm generation order; helper
            // support is appended when each indexed root is materialized.
            let generate_subterms_start = Instant::now();
            self.subterm_handler
                .generate_subterms(&mut self.bmc_builder);
            self.last_unroll_profile.insert(
                "unroll_generate_subterms".to_string(),
                generate_subterms_start.elapsed().as_secs_f64(),
            );
            // Add new variables for this depth to the solver backend.
            let add_variables_start = Instant::now();
            self.add_solver_variables();
            self.last_unroll_profile.insert(
                "unroll_add_solver_variables".to_string(),
                add_variables_start.elapsed().as_secs_f64(),
            );
            // Add the transition into the current depth and prepare its property.
            let add_assertion_start = Instant::now();
            self.add_transition_assertion();
            self.update_property();
            self.last_unroll_profile.insert(
                "unroll_add_assertion".to_string(),
                add_assertion_start.elapsed().as_secs_f64(),
            );

            // Call instantiation strategy's on_loop hook to handle instantiations at this depth
            if !self.instantiations.is_empty() {
                let on_loop_start = Instant::now();
                let instantiations_snapshot: Vec<StoredInstantiation> = self.instantiations.clone();
                self.instantiation_strategy.on_loop(
                    self.depth,
                    &instantiations_snapshot,
                    &mut self.bmc_builder,
                    &mut self.definition_materializer,
                    self.solver.as_mut(),
                    &mut self.subterm_handler,
                    self.track_instantiations,
                    &mut self.tracked_labels,
                    &mut self.asserted_instantiation_terms,
                    &mut self.num_quantifiers_instantiated,
                );
                self.last_unroll_profile.insert(
                    "unroll_instantiation_on_loop".to_string(),
                    on_loop_start.elapsed().as_secs_f64(),
                );
            }
        } else {
            self.last_unroll_profile.insert(
                "unroll_noop".to_string(),
                unroll_start.elapsed().as_secs_f64(),
            );
        }
        self.last_unroll_profile.insert(
            "unroll_total".to_string(),
            unroll_start.elapsed().as_secs_f64(),
        );
    }
}

impl ProblemContext for VmtBmcSession {
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

    fn make_unquantified_instance(&self, term: Term) -> Option<Instance> {
        smt2parser::vmt::UnquantifiedInstantiator::rewrite_with_definitions(
            term,
            self.bmc_builder.definition_frames().clone(),
        )
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
        concrete::{QualIdentifier, Sort, SyntaxBuilder, Term},
        vmt::VMTModel,
        CommandStream,
    };

    use crate::{
        auxiliary_synthesis::{
            AuxiliarySpec, FrameSpan, GuardPolicy, HistorySpec, NonMonotonicityCheckRecord,
            NonMonotonicityStatus, ProphecySpec, SynthesisTrigger,
        },
        cost_functions::array::ArrayBMCCost,
        instantiation_strategy::full_unroll::FullUnrollStrategy,
        strategies::{Abstract, ArrayRefinementState, ConcreteArrayZ3, ProofStrategy},
    };

    use super::*;

    #[test]
    fn dump_formatter_appends_property_check_and_unsat_core_commands() {
        let property: Term = "(> x@0 0)".parse().unwrap();
        let output = format_smt2_with_property_check(
            "(declare-fun x@0 () Int)\n(assert (> x@0 -1))",
            &property,
        );

        assert!(output.starts_with("(set-option :produce-unsat-cores true)\n"));
        assert!(output.contains("(assert (! (not (> x@0 0)) :named yardbird_negated_property))\n"));
        assert!(output.ends_with("(check-sat)\n(get-unsat-core)\n"));
    }

    #[test]
    fn named_assertion_formatter_names_transition_system_formulas() {
        let assertions = vec![
            NamedAssertion::new("yardbird_init_0", "(= i@0 0)".parse::<Term>().unwrap()),
            NamedAssertion::new(
                "yardbird_trans_0_to_1",
                "(= i@1 (+ i@0 1))".parse::<Term>().unwrap(),
            ),
        ];
        let output = format_named_assertions(&assertions);

        assert!(output.contains("(assert (! (= i@0 0) :named yardbird_init_0))"));
        assert!(output.contains("(assert (! (= i@1 (+ i@0 1)) :named yardbird_trans_0_to_1))"));
    }

    #[test]
    fn generated_instances_materialize_helper_definitions_at_their_anchor_frame() {
        let input = br#"
            (declare-fun x () Int)
            (define-fun x.relationship () Int (! x :next x.next))
            (define-fun next-only () Int (+ x.next 1))
            (define-fun init () Bool (! true :init true))
            (define-fun transition () Bool (! (= x.next x) :trans true))
            (define-fun property () Bool (! true :invar-property 0))
        "#;
        let commands = CommandStream::new(&input[..], SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let model = VMTModel::checked_from(commands).unwrap();
        let mut concrete_strategy = Abstract::<ArrayBMCCost>::new(
            2,
            false,
            (),
            crate::auxiliary_synthesis::AuxSynthesisConfig::default(),
            false,
        );
        let model = concrete_strategy.configure_model(model);
        let strategy: Box<dyn ProofStrategy<'_, ArrayRefinementState>> =
            Box::new(concrete_strategy);
        let mut smt = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            false,
            Box::new(FullUnrollStrategy::new()),
            false,
            None,
        );
        smt.unroll(1);

        let instance =
            ProblemContext::make_unquantified_instance(&smt, "(= next-only@0 1)".parse().unwrap())
                .unwrap();
        assert_eq!(instance.width(), 1);
        assert!(smt.add_instantiation(instance, None));

        assert!(smt
            .definition_materializer
            .declarations()
            .iter()
            .any(|command| command.to_string() == "(declare-fun next-only@0 () Int)"));
        assert!(smt
            .definition_materializer
            .definitions()
            .iter()
            .any(|term| term.to_string() == "(= next-only@0 (+ x@1 1))"));
        let dumped = smt.smt2_string_with_property_check();
        assert!(dumped.contains("(declare-fun next-only@0 () Int)"));
        assert!(dumped.contains("(assert (= next-only@0 (+ x@1 1)))"));
    }

    #[test]
    fn declares_prefixed_state_variables_at_every_unrolled_frame() {
        let input = br#"
            (declare-fun __state () Int)
            (declare-fun __state.next () Int)
            (define-fun state.relationship () Int (! __state :next __state.next))
            (define-fun init () Bool (! (= __state 0) :init true))
            (define-fun transition () Bool (! (= __state.next __state) :trans true))
            (define-fun property () Bool (! (>= __state 0) :invar-property 0))
        "#;
        let commands = CommandStream::new(&input[..], SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let model = VMTModel::checked_from(commands).unwrap();
        let strategy: Box<dyn ProofStrategy<'_, ArrayRefinementState>> =
            Box::new(ConcreteArrayZ3::new(false));
        let mut smt = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            false,
            Box::new(FullUnrollStrategy::new()),
            false,
            None,
        );

        smt.unroll(1);

        let dumped = smt.smt2_string_with_property_check();
        assert!(dumped.contains("(declare-fun __state@0 () Int)"));
        assert!(dumped.contains("(declare-fun __state@1 () Int)"));
    }

    #[test]
    fn installs_auxiliary_specs_for_existing_and_future_frames() {
        let model = VMTModel::from_path("./examples/array/array_copy.vmt").unwrap();
        let mut concrete_strategy = Abstract::<ArrayBMCCost>::new(
            4,
            false,
            (),
            crate::auxiliary_synthesis::AuxSynthesisConfig::default(),
            false,
        );
        let model = concrete_strategy.configure_model(model);
        let strategy: Box<dyn ProofStrategy<'_, ArrayRefinementState>> =
            Box::new(concrete_strategy);
        let mut smt = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            false,
            Box::new(FullUnrollStrategy::new()),
            false,
            None,
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
