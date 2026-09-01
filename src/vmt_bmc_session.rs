use std::{
    collections::{BTreeMap, HashSet},
    time::Instant,
    vec,
};

use log::debug;
use smt2parser::{
    concrete::{Command, QualIdentifier, Symbol, Term},
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
    auxiliary_synthesis::{AuxiliaryRecord, AuxiliarySpec, FrameSpan},
    instantiation_provenance::{
        InstantiationInstallResult, InstantiationProvenance, InstantiationRequest,
        StoredInstantiation,
    },
    instantiation_strategy::{
        assertion_tracker::InstantiationAssertionTracker, InstantiationContext,
        InstantiationStrategy,
    },
    interpolant::SequenceInterpolationQuery,
    problem_context::ProblemContext,
    profiling::{SolverCheckMeasurement, SolverProfileMetadata},
    solver::{
        check::{run_solver_check, SolverCheckRequest},
        new_solver_backend, PropertyCheckMode, SolverCapture, SolverCheckResult, YardbirdSolver,
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
    frame: u16,
}

impl NamedAssertion {
    fn new(label: impl Into<String>, term: Term, frame: u16) -> Self {
        Self {
            label: label.into(),
            term,
            frame,
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
    action_variables: Vec<Command>,
    init_assertion: Term,
    trans_assertion: Term,
    property_assertion: Term,
    property_check_mode: PropertyCheckMode,
    property_activation_assertions: Vec<Term>,
    property_activation_revisions: BTreeMap<u16, u32>,
    current_property_assumption: Option<Term>,
    current_property_assumption_depth: Option<u16>,
    init_and_transition_assertions: Vec<NamedAssertion>,
    model_axioms: Vec<Term>,
    model_axiom_assertions: Vec<Term>,
    theory_axiom_assertions: Vec<Term>,
    asserted_instantiation_terms: Vec<Term>,
    auxiliary_specs: Vec<AuxiliarySpec>,
    auxiliary_records: Vec<AuxiliaryRecord>,
    auxiliary_transition_assertions: Vec<Term>,
    auxiliary_property_constraints: Vec<Term>,
    depth: u16,
    instantiations: Vec<StoredInstantiation>,
    subterm_handler: SubtermHandler,
    pub variables: Vec<Variable>,
    solver: Box<dyn YardbirdSolver>,
    num_quantifiers_instantiated: u64,
    track_instantiations: bool,
    tracked_labels: Vec<crate::training::IndexedInstantiationRecord>,
    instantiation_strategy: Box<dyn InstantiationStrategy>,
    assertion_tracker: InstantiationAssertionTracker,
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

fn interpolation_assertion_frame(term: &Term, depth: u16) -> u16 {
    FrameSpan::from_term(term)
        .max_frame
        .and_then(|frame| u16::try_from(frame).ok())
        .map(|frame| frame.min(depth))
        .unwrap_or(0)
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
    ) -> anyhow::Result<Self> {
        let current_vars = vmt_model.get_all_current_variable_names();
        let next_to_current_vars = vmt_model.get_next_to_current_varible_names();
        let helper_definitions = vmt_model.get_helper_definitions().clone();
        let definition_frames =
            DefinitionFrameInfo::new(&helper_definitions, &current_vars, &next_to_current_vars);
        let init_assertion = vmt_model.get_initial_condition_for_yardbird();
        let trans_assertion = vmt_model.get_trans_condition_for_yardbird();
        let property_assertion = vmt_model.get_property_for_yardbird();
        let property_check_mode = strategy.property_check_mode();
        let model_axioms = vmt_model.get_axioms();
        let theory = strategy.get_theory_support();
        let mut logic_terms = vec![&init_assertion, &trans_assertion, &property_assertion];
        logic_terms.extend(model_axioms.iter());
        let logic = theory.get_logic_string_for_problem(&logic_terms, &vmt_model.as_commands())?;
        let solver = new_solver_backend(solver_backend, &logic, solver_capture)?;

        let mut smt = VmtBmcSession {
            sorts: vmt_model.get_sorts(),
            function_definitions: vmt_model.get_function_definitions(),
            variable_definitions: vec![],
            input_variables: vmt_model.get_input_variables(),
            action_variables: vmt_model.get_action_variables(),
            subterm_handler: SubtermHandler::new(
                init_assertion.clone(),
                trans_assertion.clone(),
                property_assertion.clone(),
            ),
            init_assertion,
            trans_assertion,
            property_assertion,
            property_check_mode,
            property_activation_assertions: vec![],
            property_activation_revisions: BTreeMap::new(),
            current_property_assumption: None,
            current_property_assumption_depth: None,
            init_and_transition_assertions: vec![],
            model_axioms,
            model_axiom_assertions: vec![],
            theory_axiom_assertions: vec![],
            asserted_instantiation_terms: vec![],
            auxiliary_specs: vec![],
            auxiliary_records: vec![],
            auxiliary_transition_assertions: vec![],
            auxiliary_property_constraints: vec![],
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
            assertion_tracker: InstantiationAssertionTracker::default(),
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

        // VMT-level function declarations are part of the problem regardless
        // of whether array operations are abstracted or sent to Z3 natively.
        for function_def in vmt_model.get_function_definitions() {
            if accepted_declarations.insert(function_def.clone()) {
                smt.solver
                    .accept_command(&function_def)
                    .expect("solver should accept VMT function declarations");
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
        smt.add_model_axioms_at_current_depth();
        smt.subterm_handler.generate_subterms(&mut smt.bmc_builder);
        smt.add_initial_assertion();
        smt.update_property();
        debug!("{:#?}", smt);
        Ok(smt)
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
        let action_variables = self.action_variables.clone();
        for action in &action_variables {
            self.add_declaration_at_current_depth(action);
        }
    }

    fn add_model_axioms_at_current_depth(&mut self) {
        for axiom in self.model_axioms.clone() {
            let indexed = self.bmc_builder.index_single_step_term(axiom);
            if self.model_axiom_assertions.contains(&indexed) {
                continue;
            }
            self.solver
                .assert_term(&indexed)
                .expect("solver should assert VMT model axioms");
            self.model_axiom_assertions.push(indexed);
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
            .push(NamedAssertion::new("yardbird_init_0", materialized.root, 0));
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
                self.depth,
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
                self.depth,
            );
        }
    }

    fn update_property(&mut self) {
        let retain_refinement_assumption = self.current_property_assumption.is_some()
            && self.current_property_assumption_depth == Some(self.depth)
            && self.property_check_mode == PropertyCheckMode::RefinementAssumptions;
        let property = if self.auxiliary_property_constraints.is_empty() {
            self.bmc_builder
                .index_single_step_term(self.property_assertion.clone())
        } else {
            let property = self.effective_property_assertion();
            self.subterm_handler
                .replace_property_term(property, &mut self.bmc_builder);
            self.subterm_handler.get_property_assert()
        };
        let materialized = self.materialize(property);
        self.subterm_handler
            .register_property_support(&materialized.support);
        self.install_materialized_support(&materialized);
        self.current_property_assumption = None;
        self.current_property_assumption_depth = None;

        if self.property_check_mode == PropertyCheckMode::Assumptions
            || retain_refinement_assumption
        {
            let property = self.subterm_handler.get_property_assert();
            self.install_property_activation(&property);
        }
    }

    fn effective_property_assertion(&self) -> Term {
        if self.auxiliary_property_constraints.is_empty() {
            return self.property_assertion.clone();
        }
        let antecedent = if self.auxiliary_property_constraints.len() == 1 {
            self.auxiliary_property_constraints[0].clone()
        } else {
            Term::Application {
                qual_identifier: QualIdentifier::simple("and"),
                arguments: self.auxiliary_property_constraints.clone(),
            }
        };
        Term::Application {
            qual_identifier: QualIdentifier::simple("=>"),
            arguments: vec![antecedent, self.property_assertion.clone()],
        }
    }

    fn install_property_activation(&mut self, property: &Term) {
        debug_assert!(self.current_property_assumption.is_none());
        let revision = self
            .property_activation_revisions
            .entry(self.depth)
            .or_default();
        let activation_name = if *revision == 0 {
            format!("yardbird_property_depth_{}", self.depth)
        } else {
            format!("yardbird_property_depth_{}_{}", self.depth, revision)
        };
        *revision += 1;
        self.solver
            .accept_command(&Command::DeclareFun {
                symbol: Symbol(activation_name.clone()),
                parameters: vec![],
                sort: crate::theory_support::bool_sort(),
            })
            .expect("solver should declare the property activation literal");
        let activation = Term::QualIdentifier(QualIdentifier::simple(activation_name));
        let negated_property = Term::Application {
            qual_identifier: QualIdentifier::simple("not"),
            arguments: vec![property.clone()],
        };
        let guarded_property = Term::Application {
            qual_identifier: QualIdentifier::simple("=>"),
            arguments: vec![activation.clone(), negated_property],
        };
        self.solver
            .assert_term(&guarded_property)
            .expect("solver should assert the guarded negated property");
        self.property_activation_assertions.push(guarded_property);
        self.current_property_assumption = Some(activation);
        self.current_property_assumption_depth = Some(self.depth);
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
        request: InstantiationRequest,
    ) -> InstantiationInstallResult {
        let trace_instantiations = log::log_enabled!(log::Level::Trace);
        let initial_count = self.instantiations.len();
        let inst_text = trace_instantiations.then(|| request.inst.to_string());
        let abstract_id_for_log = trace_instantiations.then(|| {
            request
                .provenance
                .as_ref()
                .map(|provenance| provenance.abstract_instantiation_id().to_string())
        });

        let mut context = InstantiationContext::new(
            &mut self.instantiations,
            &mut self.bmc_builder,
            &mut self.definition_materializer,
            self.solver.as_mut(),
            &mut self.subterm_handler,
            self.track_instantiations,
            &mut self.tracked_labels,
            &mut self.asserted_instantiation_terms,
            &mut self.num_quantifiers_instantiated,
            &mut self.assertion_tracker,
        );
        let result = self
            .instantiation_strategy
            .on_generate(request, &mut context);

        if trace_instantiations {
            log::trace!(
                "[yardbird::inst-trace] solver-add abstract-id={abstract_instantiation_id:?} abstract-added={} solver-assertions-added={} before={before} after={after} term={term}",
                result.abstract_instance_added,
                result.solver_assertions_added(),
                before = initial_count,
                after = self.instantiations.len(),
                term = inst_text.unwrap_or_default(),
                abstract_instantiation_id = abstract_id_for_log.unwrap_or_default(),
            );
        }
        result
    }

    pub(crate) fn to_sequence_smtinterpol(&self) -> SequenceInterpolationQuery {
        let sort_names = unique_command_lines(&self.sorts);
        let function_definitions = unique_command_lines(&self.function_definitions);
        let variable_definitions = unique_command_lines(&self.variable_definitions);
        let helper_declarations =
            unique_command_lines(&self.definition_materializer.declarations());

        let mut partitions = (0..=self.depth)
            .map(|frame| (frame, Vec::<Term>::new()))
            .collect::<BTreeMap<_, _>>();
        let mut add_inferred = |term: &Term| {
            let frame = interpolation_assertion_frame(term, self.depth);
            partitions.entry(frame).or_default().push(term.clone());
        };
        for assertion in &self.theory_axiom_assertions {
            add_inferred(assertion);
        }
        for assertion in &self.model_axiom_assertions {
            add_inferred(assertion);
        }
        for assertion in self.definition_materializer.definitions() {
            add_inferred(&assertion);
        }
        for assertion in &self.asserted_instantiation_terms {
            add_inferred(assertion);
        }
        for assertion in &self.init_and_transition_assertions {
            partitions
                .entry(assertion.frame)
                .or_default()
                .push(assertion.term.clone());
        }
        partitions
            .entry(self.depth)
            .or_default()
            .push(Term::Application {
                qual_identifier: QualIdentifier::simple("not"),
                arguments: vec![self.subterm_handler.get_property_assert()],
            });

        let partition_asserts = partitions
            .into_iter()
            .enumerate()
            .map(|(partition_index, (_frame, assertions))| {
                let conjunction = Term::Application {
                    qual_identifier: QualIdentifier::simple("and"),
                    arguments: assertions,
                };
                smtinterpol_utils::assert_term_interpolant(partition_index, &conjunction)
            })
            .collect::<Vec<_>>()
            .join("\n");
        let interpolant_command = smtinterpol_utils::get_interpolant_command(self.depth as usize);
        let options = smtinterpol_utils::options_for_logic(&self.logic);
        let smt2 = format!(
            "{options}\n{sort_names}\n{function_definitions}\n{variable_definitions}\n{helper_declarations}\n{partition_asserts}\n{interpolant_command}"
        );
        SequenceInterpolationQuery {
            smt2,
            depth: self.depth,
            logic: self.logic.clone(),
            interpolant_frames: (0..self.depth).collect(),
        }
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
        let mut property_changed = false;
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

            if let Some(property_constraint) = &spec.property_constraint {
                self.auxiliary_property_constraints
                    .push(property_constraint.clone());
                property_changed = true;
            }

            self.auxiliary_records.push(spec.record(self.depth));
            self.auxiliary_specs.push(spec);
        }
        if property_changed {
            self.update_property();
        }
        Ok(())
    }

    pub(crate) fn get_auxiliary_records(&self) -> &[AuxiliaryRecord] {
        &self.auxiliary_records
    }

    pub(crate) fn get_auxiliary_specs(&self) -> &[AuxiliarySpec] {
        &self.auxiliary_specs
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
            format_assertions(&self.model_axiom_assertions),
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
            abstract_instantiation_id: Option<String>,
            frame: u16,
            substitution: Vec<crate::instantiation_provenance::InstantiationSubstitution>,
            in_core: bool,
        }

        let core_set: std::collections::HashSet<_> = core_labels.iter().collect();

        let tracked_instantiations: Vec<TrackedInst> = self
            .tracked_labels
            .iter()
            .map(|record| TrackedInst {
                label: record.label.clone(),
                term: record.term.clone(),
                abstract_instantiation_id: record.abstract_instantiation_id.clone(),
                frame: record.frame,
                substitution: record.substitution.clone(),
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
        self.assert_auxiliary_term(indexed_transition, label, depth);
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
        self.assert_auxiliary_term(indexed_init, label, 0);
        self.bmc_builder.set_depth(current_depth);
    }

    fn assert_auxiliary_term(&mut self, term: Term, label: impl Into<String>, frame: u16) {
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
            .push(NamedAssertion::new(label, materialized.root, frame));
    }
}

impl VmtBmcSession {
    /// Checks the satisfiability of BMC `self.bmc_builder.depth` under the
    /// negated property. Scoped checks push the property temporarily;
    /// assumption checks enable a permanently guarded property literal.
    ///
    /// NOTE: We have to get the model here and set it because once we pop the solver, that model will
    /// be lost.
    pub(crate) fn check_property(&mut self) -> SolverCheckResult {
        self.last_check_profile.clear();
        self.last_solver_check_profile = None;
        let using_assumptions = self.current_property_assumption.is_some();
        let property_assertion_count =
            self.property_activation_assertions.len() + usize::from(!using_assumptions);
        let assertion_count = (self.model_axiom_assertions.len()
            + self.theory_axiom_assertions.len()
            + self.init_and_transition_assertions.len()
            + self.asserted_instantiation_terms.len()
            + property_assertion_count) as u64;
        let property = self.subterm_handler.get_property_assert();
        let assumptions = self
            .current_property_assumption
            .iter()
            .cloned()
            .collect::<Vec<_>>();
        let temporary_negated_property = (!using_assumptions).then_some(&property);
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
                temporary_negated_property,
                assumptions: &assumptions,
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

        if outcome.result == SolverCheckResult::Sat
            && self.property_check_mode == PropertyCheckMode::RefinementAssumptions
            && self.current_property_assumption.is_none()
        {
            self.install_property_activation(&property);
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
            self.add_model_axioms_at_current_depth();
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
                let mut context = InstantiationContext::new(
                    &mut self.instantiations,
                    &mut self.bmc_builder,
                    &mut self.definition_materializer,
                    self.solver.as_mut(),
                    &mut self.subterm_handler,
                    self.track_instantiations,
                    &mut self.tracked_labels,
                    &mut self.asserted_instantiation_terms,
                    &mut self.num_quantifiers_instantiated,
                    &mut self.assertion_tracker,
                );
                self.instantiation_strategy
                    .on_loop(self.depth, &mut context);
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

    fn get_source_subterms(&self) -> Vec<&Term> {
        self.subterm_handler.get_source_subterms()
    }

    fn separates_source_subterms(&self) -> bool {
        true
    }

    fn get_solver_statistics(&self) -> SolverStatistics {
        let mut statistics = self.solver.get_solver_statistics();
        self.assertion_tracker
            .metrics()
            .add_to_solver_statistics(&mut statistics);
        statistics.add_count(
            "yardbird.helper definition equalities",
            self.definition_materializer.definitions().len() as u64,
        );
        statistics
    }

    fn get_reason_unknown(&self) -> Option<String> {
        self.solver.get_reason_unknown()
    }

    fn add_instantiation(&mut self, request: InstantiationRequest) -> InstantiationInstallResult {
        self.add_instantiation(request)
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

    fn get_number_instantiation_assertions_added(&self) -> u64 {
        self.assertion_tracker.metrics().unique_assertions
    }

    fn make_unquantified_instance(&self, term: Term) -> Option<Instance> {
        smt2parser::vmt::UnquantifiedInstantiator::rewrite_with_definitions(
            term,
            self.bmc_builder.definition_frames().clone(),
        )
    }

    fn make_provenanced_unquantified_instance(
        &self,
        term: Term,
        provenance: InstantiationProvenance,
    ) -> Option<InstantiationRequest> {
        let (abstract_instantiation_id, substitution) = provenance.into_parts();
        let (inst, relative_substitution) =
            smt2parser::vmt::UnquantifiedInstantiator::rewrite_with_definitions_and_substitution(
                term,
                self.bmc_builder.definition_frames().clone(),
                substitution,
            )?;
        Some(InstantiationRequest::provenanced(
            inst,
            InstantiationProvenance::new(abstract_instantiation_id, relative_substitution),
        ))
    }

    fn get_init_and_transition_subterms(&self) -> Vec<String> {
        let mut trans = self.subterm_handler.get_transition_system_subterms();
        trans.extend(self.subterm_handler.get_initial_subterms());
        trans.extend(self.subterm_handler.get_instantiation_subterms());
        trans
    }

    fn get_source_init_and_transition_subterms(&self) -> Vec<String> {
        let mut trans = self.subterm_handler.get_transition_system_subterms();
        trans.extend(self.subterm_handler.get_initial_subterms());
        trans
    }

    fn get_property_subterms(&self) -> Vec<String> {
        self.subterm_handler.get_property_subterms()
    }

    fn get_reads_and_writes(&self) -> smt2parser::vmt::ReadsAndWrites {
        self.subterm_handler.get_reads_and_writes()
    }

    fn get_array_candidate_catalog(&self) -> crate::problem_context::ArrayCandidateCatalog {
        let mut source_terms = self.subterm_handler.get_transition_system_subterms();
        source_terms.extend(self.subterm_handler.get_initial_subterms());
        source_terms.extend(self.subterm_handler.get_property_subterms());
        crate::problem_context::ArrayCandidateCatalog {
            source_grounded: crate::problem_context::ArrayCandidatePool {
                terms: source_terms,
                reads_and_writes: self.subterm_handler.get_source_reads_and_writes(),
            },
            derived: crate::problem_context::ArrayCandidatePool {
                terms: self.subterm_handler.get_instantiation_subterms(),
                reads_and_writes: self.subterm_handler.get_derived_reads_and_writes(),
            },
        }
    }

    fn get_array_types(&self) -> Vec<(String, String)> {
        // For VMT mode, array types are managed by the strategy's discovered_array_types
        // This is a fallback that returns empty - VMT mode uses configure_model instead
        vec![]
    }

    fn frame_transition_formula(&self, term: Term, frame: u16) -> Option<Term> {
        let mut builder = self.bmc_builder.clone();
        builder.set_depth(frame);
        Some(builder.index_single_step_term(term))
    }

    fn install_auxiliary_specs(&mut self, specs: Vec<AuxiliarySpec>) -> anyhow::Result<()> {
        self.install_auxiliary_specs(specs)
    }

    fn get_auxiliary_records(&self) -> Vec<AuxiliaryRecord> {
        self.get_auxiliary_records().to_vec()
    }

    fn get_auxiliary_specs(&self) -> Vec<AuxiliarySpec> {
        self.get_auxiliary_specs().to_vec()
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
            AuxiliarySpec, FrameSpan, GuardPolicy, HistoryCaptureMode, HistorySpec,
            NonMonotonicityCheckRecord, NonMonotonicityStatus, ProphecySpec, SynthesisTrigger,
        },
        cost_functions::array::ArrayBMCCost,
        instantiation_strategy::{
            full_unroll::FullUnrollStrategy, schema_batch::SchemaBatchStrategy,
        },
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
            NamedAssertion::new("yardbird_init_0", "(= i@0 0)".parse::<Term>().unwrap(), 0),
            NamedAssertion::new(
                "yardbird_trans_0_to_1",
                "(= i@1 (+ i@0 1))".parse::<Term>().unwrap(),
                1,
            ),
        ];
        let output = format_named_assertions(&assertions);

        assert!(output.contains("(assert (! (= i@0 0) :named yardbird_init_0))"));
        assert!(output.contains("(assert (! (= i@1 (+ i@0 1)) :named yardbird_trans_0_to_1))"));
    }

    #[test]
    fn sequence_interpolation_groups_native_array_bmc_assertions_by_frame() {
        let input = br#"
            (declare-fun x () Int)
            (declare-fun x_next () Int)
            (define-fun .x () Int (! x :next x_next))
            (declare-fun a () (Array Int Int))
            (declare-fun a_next () (Array Int Int))
            (define-fun .a () (Array Int Int) (! a :next a_next))
            (define-fun init () Bool (!
                (and (= x 0) (= a ((as const (Array Int Int)) 0)))
                :init true))
            (define-fun transition () Bool (!
                (and (= x_next (+ x 1)) (= a_next (store a x x)))
                :trans true))
            (define-fun property () Bool (! (>= x 0) :invar-property 0))
        "#;
        let commands = CommandStream::new(&input[..], SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let model = VMTModel::checked_from(commands).unwrap();
        let mut strategy: Box<dyn ProofStrategy<'_, ArrayRefinementState>> =
            Box::new(ConcreteArrayZ3::new(false));
        let model = strategy.configure_model(model);
        let mut smt = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            false,
            Box::new(FullUnrollStrategy::new()),
            false,
            None,
        )
        .unwrap();
        smt.unroll(1);
        smt.unroll(2);

        let query = smt.to_sequence_smtinterpol();

        assert_eq!(query.depth, 2);
        assert_eq!(query.logic, "QF_AUFLIA");
        assert_eq!(query.interpolant_frames, [0, 1]);
        assert!(query.smt2.contains("(set-logic QF_AUFLIA)"));
        assert!(query.smt2.contains(":named A"));
        assert!(query.smt2.contains(":named B"));
        assert!(query.smt2.contains(":named C"));
        assert!(query.smt2.contains("(= x@1 (+ x@0 1))"));
        assert!(query.smt2.contains("(= x@2 (+ x@1 1))"));
        assert!(query.smt2.contains("(not (>= x@2 0))"));
        assert!(query.smt2.contains("(store a@1 x@1 x@1)"));
    }

    #[test]
    fn schema_batch_piggybacks_stored_placements_on_normal_generation() {
        let input = br#"
            (declare-fun x () Int)
            (declare-fun x_next () Int)
            (define-fun .x () Int (! x :next x_next))
            (declare-fun a () (Array Int Int))
            (declare-fun a_next () (Array Int Int))
            (define-fun .a () (Array Int Int) (! a :next a_next))
            (define-fun init () Bool (!
                (and (= x 0) (= a ((as const (Array Int Int)) 0)))
                :init true))
            (define-fun transition () Bool (!
                (and (= x_next (+ x 1)) (= a_next a))
                :trans true))
            (define-fun property () Bool (! false :invar-property 0))
        "#;
        let commands = CommandStream::new(&input[..], SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let model = VMTModel::checked_from(commands).unwrap();
        let mut concrete_strategy = ConcreteArrayZ3::new(false);
        let model = concrete_strategy.configure_model(model);
        let strategy: Box<dyn ProofStrategy<'_, ArrayRefinementState>> =
            Box::new(concrete_strategy);
        let mut smt = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            false,
            Box::new(SchemaBatchStrategy::new()),
            false,
            None,
        )
        .unwrap();

        assert_eq!(smt.check_property(), SolverCheckResult::Sat);
        for term in ["(<= x@0 0)", "(= x@0 0)"] {
            let instance =
                ProblemContext::make_unquantified_instance(&smt, term.parse::<Term>().unwrap())
                    .unwrap();
            let result = smt.add_instantiation(InstantiationRequest::untracked(instance));
            assert!(result.abstract_instance_added);
            assert_eq!(result.indexed_assertions_added, 0);
        }

        smt.unroll(1);
        assert_eq!(smt.check_property(), SolverCheckResult::Sat);
        let trigger =
            ProblemContext::make_unquantified_instance(&smt, "(>= x@0 0)".parse::<Term>().unwrap())
                .unwrap();
        let result = smt.add_instantiation(InstantiationRequest::untracked(trigger));

        assert!(result.abstract_instance_added);
        assert_eq!(result.indexed_assertions_added, 0);
        assert_eq!(smt.get_number_instantiations_added(), 2);
        assert_eq!(smt.check_property(), SolverCheckResult::Unsat);
        assert_eq!(
            smt.get_solver_statistics()
                .get_f64("yardbird.schema placement violations"),
            Some(2.0)
        );
        assert_eq!(
            smt.get_solver_statistics()
                .get_f64("yardbird.schema batch passes"),
            Some(2.0)
        );
    }

    #[test]
    fn generated_instances_materialize_helper_definitions_at_their_anchor_frame() {
        let input = br#"
            (declare-fun x () Int)
            (define-fun x.relationship () Int (! x :next x.next))
            (declare-fun a () (Array Int Int))
            (define-fun a.relationship () (Array Int Int) (! a :next a.next))
            (define-fun next-only () Int (+ x.next 1))
            (define-fun init () Bool (! true :init true))
            (define-fun transition () Bool (!
                (and (= x.next x) (= a.next (store a 0 (select a 0))))
                :trans true))
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
        )
        .unwrap();
        smt.unroll(1);

        let instance =
            ProblemContext::make_unquantified_instance(&smt, "(= next-only@0 1)".parse().unwrap())
                .unwrap();
        assert_eq!(instance.width(), 1);
        assert!(
            smt.add_instantiation(InstantiationRequest::untracked(instance))
                .abstract_instance_added
        );

        let first =
            ProblemContext::make_unquantified_instance(&smt, "(= x@0 1)".parse().unwrap()).unwrap();
        let first = smt.add_instantiation(InstantiationRequest::untracked(first));
        assert!(first.solver_assertions_added() > 0);
        let reversed =
            ProblemContext::make_unquantified_instance(&smt, "(= 1 x@0)".parse().unwrap()).unwrap();
        let reversed = smt.add_instantiation(InstantiationRequest::untracked(reversed));
        assert!(reversed.abstract_instance_added);
        assert_eq!(reversed.solver_assertions_added(), 0);
        assert_eq!(
            reversed.indexed_assertions_attempted,
            reversed.indexed_assertions_deduplicated
        );

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
            (declare-fun a () (Array Int Int))
            (define-fun a.relationship () (Array Int Int) (! a :next a.next))
            (define-fun init () Bool (! (= __state 0) :init true))
            (define-fun transition () Bool (!
                (and (= __state.next __state) (= a.next (store a 0 (select a 0))))
                :trans true))
            (define-fun property () Bool (! (>= __state 0) :invar-property 0))
        "#;
        let commands = CommandStream::new(&input[..], SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let model = VMTModel::checked_from(commands).unwrap();
        let mut strategy: Box<dyn ProofStrategy<'_, ArrayRefinementState>> =
            Box::new(ConcreteArrayZ3::new(false));
        let model = strategy.configure_model(model);
        let mut smt = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            false,
            Box::new(FullUnrollStrategy::new()),
            false,
            None,
        )
        .unwrap();

        smt.unroll(1);

        let dumped = smt.smt2_string_with_property_check();
        assert!(dumped.contains("(declare-fun __state@0 () Int)"));
        assert!(dumped.contains("(declare-fun __state@1 () Int)"));
    }

    #[test]
    fn declares_action_variables_at_every_unrolled_frame() {
        let input = br#"
            (declare-fun state () Int)
            (declare-fun state.next () Int)
            (define-fun state.relationship () Int (! state :next state.next))
            (declare-fun a () (Array Int Int))
            (declare-fun a.next () (Array Int Int))
            (define-fun a.relationship () (Array Int Int) (! a :next a.next))
            (declare-fun step () Bool)
            (define-fun step.relationship () Bool (! step :action 0))
            (define-fun init () Bool (! (= state 0) :init true))
            (define-fun transition () Bool (!
                (and (= a.next a) (=> step (= state.next (+ state 1))))
                :trans true))
            (define-fun property () Bool (! (>= state 0) :invar-property 0))
        "#;
        let commands = CommandStream::new(&input[..], SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let model = VMTModel::checked_from(commands).unwrap();
        let mut strategy: Box<dyn ProofStrategy<'_, ArrayRefinementState>> =
            Box::new(ConcreteArrayZ3::new(false));
        let model = strategy.configure_model(model);
        let mut smt = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            false,
            Box::new(FullUnrollStrategy::new()),
            false,
            None,
        )
        .unwrap();

        smt.unroll(1);

        let dumped = smt.smt2_string_with_property_check();
        assert!(dumped.contains("(declare-fun step@0 () Bool)"));
        assert!(dumped.contains("(declare-fun step@1 () Bool)"));
    }

    #[test]
    fn concrete_session_registers_declared_uninterpreted_functions() {
        let input = br#"
            (declare-fun a () (Array Int Int))
            (declare-fun a.next () (Array Int Int))
            (define-fun a.relationship () (Array Int Int) (! a :next a.next))
            (declare-fun P (Int) Bool)
            (define-fun init () Bool (! true :init true))
            (define-fun transition () Bool (!
                (= a.next (store a 0 0))
                :trans true))
            (define-fun property () Bool (! (P (select a 0)) :invar-property 0))
        "#;
        let commands = CommandStream::new(&input[..], SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let model = VMTModel::checked_from(commands).unwrap();
        let mut strategy: Box<dyn ProofStrategy<'_, ArrayRefinementState>> =
            Box::new(ConcreteArrayZ3::new(false));
        let model = strategy.configure_model(model);

        let mut smt = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            false,
            Box::new(FullUnrollStrategy::new()),
            false,
            None,
        )
        .unwrap();

        let _ = smt.check_property();

        assert!(smt
            .smt2_string_with_property_check()
            .contains("(declare-fun P (Int) Bool)"));
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
        )
        .with_property_check_mode(PropertyCheckMode::Assumptions);
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
        )
        .unwrap();

        smt.unroll(1);
        smt.unroll(2);
        assert_eq!(
            smt.current_property_assumption
                .as_ref()
                .unwrap()
                .to_string(),
            "yardbird_property_depth_2"
        );
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
                capture_term: Term::QualIdentifier(QualIdentifier::simple("i_next")),
                capture_guard: Term::QualIdentifier(QualIdentifier::simple("true")),
                capture_mode: HistoryCaptureMode::LastOccurrence,
                initial_value: None,
            },
            prophecy: Some(ProphecySpec {
                name: "yb_prop_test".to_string(),
                next_name: "yb_prop_test_next".to_string(),
                sort: int_sort,
                initial_value: None,
            }),
            localized_axiom: Some(
                "(= (Read_Int_Int (Write_Int_Int a i i) yb_prop_test) (Read_Int_Int a yb_prop_test))"
                    .parse()
                    .unwrap(),
            ),
            property_constraint: Some("(= yb_prop_test yb_hist_test)".parse().unwrap()),
            guard_policy: GuardPolicy::True,
            trigger: SynthesisTrigger::NonLocal,
            non_monotonicity_check: NonMonotonicityCheckRecord {
                status: NonMonotonicityStatus::Pending,
                source_term: "(= i@0 i@2)".to_string(),
                localized_term: Some("(= i yb_prop_test)".to_string()),
                source_frame_span: FrameSpan::from_term(&"(= i@0 i@2)".parse().unwrap()),
                localized_frame_span: Some(FrameSpan::from_term(
                    &"(= i yb_prop_test)".parse().unwrap(),
                )),
                note: "test".to_string(),
            },
        };

        smt.install_auxiliary_specs(vec![spec]).unwrap();
        assert_eq!(smt.get_auxiliary_records().len(), 1);
        assert_eq!(
            smt.current_property_assumption
                .as_ref()
                .unwrap()
                .to_string(),
            "yardbird_property_depth_2_1"
        );
        let interpolant_problem = smt.to_sequence_smtinterpol().smt2;
        assert!(interpolant_problem.contains("yb_hist_test@2"));
        assert!(interpolant_problem.contains("yb_prop_test@0"));
        assert!(interpolant_problem.contains("(=> (= yb_prop_test@2 yb_hist_test@2)"));
        assert!(interpolant_problem
            .contains("(Read_Int_Int (Write_Int_Int a@0 i@0 i@0) yb_prop_test@0)"));
        assert!(interpolant_problem
            .contains("(Read_Int_Int (Write_Int_Int a@1 i@1 i@1) yb_prop_test@1)"));

        smt.unroll(3);
        assert_eq!(
            smt.current_property_assumption
                .as_ref()
                .unwrap()
                .to_string(),
            "yardbird_property_depth_3"
        );
        let interpolant_problem = smt.to_sequence_smtinterpol().smt2;
        assert!(interpolant_problem.contains("yb_hist_test@3"));
        assert!(interpolant_problem.contains("yb_prop_test@3"));
        assert!(interpolant_problem
            .contains("(Read_Int_Int (Write_Int_Int a@2 i@2 i@2) yb_prop_test@2)"));
    }
}
