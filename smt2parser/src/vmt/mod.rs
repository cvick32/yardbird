use std::{collections::HashMap, fs::File, io::Write, path::Path};

use action::Action;
use array_abstractor::ArrayAbstractor;
use array_term_simplifier::ArrayTermSimplifier;
use axiom::Axiom;
use bmc::BMCBuilder;
use definition_graph::{DefinitionFrameInfo, DefinitionGraph, MetadataAliasExpander};
use definition_materializer::DefinitionMaterializer;
use itertools::Itertools;
use log::{debug, info};
use smt::SMTProblem;
use utils::{classify_variables, get_and_terms, get_annotated_term};
use variable::Variable;

use crate::{
    concrete::{self, Command, FunctionDec, Identifier, Sort, Symbol, SyntaxBuilder, Term},
    constant_abstraction::ConstantAbstractor,
    let_extract::LetExtract,
    CommandStream,
};

pub use quantified_instantiator::{Instance, QuantifiedInstantiator, UnquantifiedInstantiator};
pub use reads_and_write::ReadsAndWrites;

static PROPERTY_ATTRIBUTE: &str = "invar-property";
static TRANSITION_ATTRIBUTE: &str = "trans";
static INITIAL_ATTRIBUTE: &str = "init";

mod action;
pub mod array_abstractor;
mod array_axiom_frame_num_getter;
pub mod array_term_simplifier;
mod axiom;
pub mod bmc;
pub mod canonicalize_boolean;
pub mod definition_graph;
pub mod definition_materializer;
pub mod non_boolean_subterms;
pub mod numbered_to_symbolic;
pub mod quantified_instantiator;
mod reads_and_write;
mod smt;
pub mod smtinterpol_utils;
mod utils;
pub mod variable;

pub static VARIABLE_FRAME_DELIMITER: &str = "@";
pub static NEXT_VARIABLE_NAME: &str = "next";

/// Splits a BMC-indexed symbol into its original symbol and signed frame.
///
/// SMT-LIB quoted symbols keep their frame inside the surrounding pipes, so
/// `|state.value@3|` maps back to `|state.value|` at frame 3. Symbols whose
/// final `@` suffix is not numeric are ordinary identifiers, not framed ones.
pub fn split_framed_symbol(symbol: &str) -> Option<(String, i64)> {
    let (body, quoted) = match symbol.strip_prefix('|').and_then(|s| s.strip_suffix('|')) {
        Some(body) => (body, true),
        None => (symbol, false),
    };
    let (base, frame) = body.rsplit_once(VARIABLE_FRAME_DELIMITER)?;
    let frame = frame.parse().ok()?;
    let base = if quoted {
        format!("|{base}|")
    } else {
        base.to_string()
    };
    Some((base, frame))
}

pub fn format_framed_symbol(symbol: &str, frame: impl std::fmt::Display) -> String {
    match symbol.strip_prefix('|').and_then(|s| s.strip_suffix('|')) {
        Some(body) => format!("|{body}{VARIABLE_FRAME_DELIMITER}{frame}|"),
        None => format!("{symbol}{VARIABLE_FRAME_DELIMITER}{frame}"),
    }
}

fn is_assert_true(command: &Command) -> bool {
    matches!(
        command,
        Command::Assert {
            term: Term::QualIdentifier(concrete::QualIdentifier::Simple {
                identifier: Identifier::Simple { symbol },
            }),
        } if symbol.0 == "true"
    )
}

/// VMTModel represents a transition system given in VMT format.
/// The VMT specification is no longer available but there is an example here:
/// https://es-static.fbk.eu/people/griggio/ic3ia/
#[derive(Clone, Debug)]
pub struct VMTModel {
    info: Vec<Command>,
    sorts: Vec<Command>,
    state_variables: Vec<Variable>,
    input_variables: Vec<Command>,
    function_definitions: Vec<Command>,
    helper_definitions: DefinitionGraph,
    actions: Vec<Action>,
    _axioms: Vec<Axiom>,
    initial_condition: Term,
    transition_condition: Term,
    property_condition: Term,
}

#[derive(Debug, thiserror::Error)]
pub enum VMTError {
    #[error("unsupported command in VMT input: {0}")]
    UnknownCommand(String),
    #[error("failed to read VMT input: {0}")]
    FileError(#[from] std::io::Error),
    #[error("failed to parse SMT-LIB input: {0}")]
    VisitorError(#[from] concrete::Error),
    #[error("missing required VMT attribute :{0}")]
    MissingSystemComponent(&'static str),
    #[error("VMT attribute :{0} is defined more than once")]
    DuplicateSystemComponent(&'static str),
    #[error("cyclic zero-argument define-fun involving {0}")]
    CyclicDefinition(String),
    #[error("zero-argument define-fun {0} is defined more than once")]
    DuplicateDefinition(String),
}

impl VMTModel {
    pub fn from_path(path: impl AsRef<Path>) -> Result<Self, VMTError> {
        let file = std::fs::File::open(path.as_ref())?;
        let reader = std::io::BufReader::new(file);
        let command_stream = CommandStream::new(
            reader,
            SyntaxBuilder,
            Some(path.as_ref().to_string_lossy().to_string()),
        );
        VMTModel::checked_from(
            command_stream
                .into_iter()
                .collect::<Result<Vec<_>, concrete::Error>>()?,
        )
    }

    pub fn checked_from(commands: Vec<Command>) -> Result<Self, VMTError> {
        let mut metadata_alias_expander = MetadataAliasExpander::from_commands(&commands);
        let trailing_assert_true_start = commands
            .iter()
            .rposition(|command| !is_assert_true(command))
            .map_or(0, |index| index + 1);
        let mut info = vec![];
        let mut variable_commands: HashMap<String, Command> = HashMap::new();
        let mut variable_declaration_order = vec![];
        let mut sorts: Vec<Command> = vec![];
        let mut variable_relationships = vec![];
        let mut function_definitions = vec![];
        let mut helper_definition_commands = vec![];
        let mut initial_condition = None;
        let mut transition_condition = None;
        let mut property_condition = None;

        for (index, command) in commands.iter().enumerate() {
            if index >= trailing_assert_true_start {
                continue;
            }

            let mut has_vmt_metadata = false;
            for (attribute, component) in [
                (INITIAL_ATTRIBUTE, &mut initial_condition),
                (TRANSITION_ATTRIBUTE, &mut transition_condition),
                (PROPERTY_ATTRIBUTE, &mut property_condition),
            ] {
                if let Some(term) = get_annotated_term(command, attribute) {
                    let term = metadata_alias_expander.expand(term)?;
                    if component.replace(term).is_some() {
                        return Err(VMTError::DuplicateSystemComponent(attribute));
                    }
                    has_vmt_metadata = true;
                }
            }

            if let Command::DefineFun { sig, .. } = command {
                for attribute in ["next", "action", "axiom"] {
                    if let Some(term) = get_annotated_term(command, attribute) {
                        variable_relationships.push(Command::DefineFun {
                            sig: sig.clone(),
                            term: metadata_alias_expander.expand(term)?,
                        });
                        has_vmt_metadata = true;
                    }
                }
            }

            if has_vmt_metadata {
                continue;
            }

            // Check whether a variable should be action, state, or local.
            match command {
                Command::SetInfo { .. } => {
                    info.push(command.clone());
                }
                Command::DeclareFun {
                    symbol,
                    parameters,
                    sort: _,
                } => {
                    if parameters.is_empty() {
                        if !variable_commands.contains_key(&symbol.0) {
                            variable_declaration_order.push(symbol.0.clone());
                        }
                        variable_commands.insert(symbol.0.clone(), command.clone());
                    } else {
                        function_definitions.push(command.clone());
                    }
                }
                Command::DefineFun { sig, term } => {
                    if sig.parameters.is_empty() {
                        helper_definition_commands.push(Command::DefineFun {
                            sig: sig.clone(),
                            term: metadata_alias_expander.expand(term.clone())?,
                        });
                    } else {
                        function_definitions.push(Command::DefineFun {
                            sig: sig.clone(),
                            term: term.clone(),
                        });
                    }
                }
                Command::DeclareSort {
                    symbol: _,
                    arity: _,
                } => {
                    sorts.push(command.clone());
                }
                _ => return Err(VMTError::UnknownCommand(command.to_string())),
            }
        }

        let initial_condition =
            initial_condition.ok_or(VMTError::MissingSystemComponent(INITIAL_ATTRIBUTE))?;
        let transition_condition =
            transition_condition.ok_or(VMTError::MissingSystemComponent(TRANSITION_ATTRIBUTE))?;
        let property_condition =
            property_condition.ok_or(VMTError::MissingSystemComponent(PROPERTY_ATTRIBUTE))?;

        let classified_variables = classify_variables(
            variable_relationships,
            variable_commands,
            variable_declaration_order,
        );
        let helper_definitions = DefinitionGraph::from_commands(helper_definition_commands)?;

        Ok(VMTModel {
            info,
            sorts,
            function_definitions,
            helper_definitions,
            state_variables: classified_variables.state_variables,
            input_variables: classified_variables.input_variables,
            actions: classified_variables.actions,
            _axioms: classified_variables.axioms,
            initial_condition,
            transition_condition,
            property_condition,
        })
    }

    /// Clones the current model, rewrites all usages of Arrays into uninterpreted functions
    /// and returns the abstracted VMTModel.
    /// Abstract array theory and return both the abstracted model and discovered array types.
    /// Returns (abstracted_model, discovered_types) where discovered_types is a vector of
    /// (index_sort, value_sort) pairs for all array types found in the model.
    pub fn abstract_array_theory(&self) -> (VMTModel, Vec<(String, String)>) {
        self.abstract_array_theory_with_preprocessing(false)
    }

    pub fn abstract_array_theory_with_preprocessing(
        &self,
        preprocess_exact_read_after_write: bool,
    ) -> (VMTModel, Vec<(String, String)>) {
        let mut abstractor =
            ArrayAbstractor::with_helper_definitions(self.helper_definitions.names());
        let commands = self.as_commands();
        let mut simplifier = ArrayTermSimplifier::from_commands(&commands);
        let mut abstracted_commands = vec![];
        for command in commands {
            let command = if preprocess_exact_read_after_write {
                simplifier.simplify_command(command)
            } else {
                command
            };
            abstracted_commands.push(command.accept(&mut abstractor).unwrap());
        }
        if preprocess_exact_read_after_write {
            log::debug!(
                "simplified {} exact native read-after-write terms before abstraction",
                simplifier.exact_read_after_write_rewrites()
            );
        }
        let mut array_definitions = abstractor.get_array_type_definitions();
        array_definitions.extend(abstracted_commands);

        // Extract discovered types from the abstractor
        let discovered_types = abstractor.sorted_array_types();

        (
            VMTModel::checked_from(array_definitions).unwrap(),
            discovered_types,
        )
    }

    pub fn abstract_constants_over(mut self, depth: u16) -> Self {
        let mut constant_abstactor = ConstantAbstractor::new(depth);
        self.initial_condition = self
            .initial_condition
            .accept(&mut constant_abstactor)
            .unwrap();
        self.transition_condition = self
            .transition_condition
            .accept(&mut constant_abstactor)
            .unwrap();
        self.property_condition = self
            .property_condition
            .accept(&mut constant_abstactor)
            .unwrap();

        self.state_variables
            .append(&mut constant_abstactor.variables());
        self.transition_condition =
            constant_abstactor.transition_properties(self.transition_condition);
        self.property_condition = constant_abstactor.invariant_properties(self.property_condition);
        // println!(
        //     "decl:\n  {}",
        //     self.state_variables
        //         .iter()
        //         .map(|x| format!("{} -> {} [{}]", x.current, x.next, x.relationship))
        //         .collect::<Vec<_>>()
        //         .join("  \n")
        // );
        // println!("init: {}", self.initial_condition);
        // println!("tran: {}", self.transition_condition);
        // println!("prop: {}", self.property_condition);

        self
    }

    pub fn unroll(&self, length: u16) -> SMTProblem {
        let mut builder = self.bmc_builder();
        let mut definitions = DefinitionMaterializer::new(
            self.helper_definitions.clone(),
            builder.definition_frames().clone(),
        );
        let mut smt_problem = SMTProblem::new(&self.sorts, &self.function_definitions);

        smt_problem.add_assertion(&self.initial_condition, &mut builder, &mut definitions);
        for _ in 0..length {
            // Must add variable definitions for each variable at each time step.
            smt_problem.add_variable_definitions(
                &self.state_variables,
                &self.input_variables,
                &self.actions,
                &mut builder,
            );
            smt_problem.add_assertion(&self.transition_condition, &mut builder, &mut definitions);
            builder.add_step();
        }
        // Don't forget the variable definitions at time `length`.
        smt_problem.add_variable_definitions(
            &self.state_variables,
            &self.input_variables,
            &self.actions,
            &mut builder,
        );
        smt_problem.add_property_assertion(
            &self.property_condition,
            &mut builder,
            &mut definitions,
        );
        assert!(
            smt_problem.root_assertion_count() == (length + 1).into(),
            "Unrolling gives incorrect number of steps {} for length {}.",
            smt_problem.init_and_trans_length(),
            length
        );
        smt_problem
    }

    pub fn get_initial_condition_for_yardbird(&self) -> Term {
        self.unwrap_attributes(&self.initial_condition)
    }

    pub fn get_trans_condition_for_yardbird(&self) -> Term {
        self.unwrap_attributes(&self.transition_condition)
    }

    pub fn get_property_for_yardbird(&self) -> Term {
        self.unwrap_attributes(&self.property_condition)
    }

    fn unwrap_attributes(&self, attribute_term: &Term) -> Term {
        match attribute_term {
            Term::Attributes {
                term,
                attributes: _,
            } => LetExtract::substitute(*term.clone()),
            _ => panic!("Ill-formatted VMT condition: {}", self.initial_condition),
        }
    }

    pub fn get_initial_term(&self) -> SMTProblem {
        let mut builder = self.bmc_builder();
        let mut definitions = DefinitionMaterializer::new(
            self.helper_definitions.clone(),
            builder.definition_frames().clone(),
        );
        let mut smt_problem = SMTProblem::new(&self.sorts, &self.function_definitions);
        smt_problem.add_variable_definitions(
            &self.state_variables,
            &self.input_variables,
            &self.actions,
            &mut builder,
        );
        smt_problem.add_assertion(&self.initial_condition, &mut builder, &mut definitions);
        smt_problem
    }

    pub fn get_trans_term(&self) -> SMTProblem {
        let mut builder = self.bmc_builder();
        let mut definitions = DefinitionMaterializer::new(
            self.helper_definitions.clone(),
            builder.definition_frames().clone(),
        );
        let mut smt_problem = SMTProblem::new(&self.sorts, &self.function_definitions);

        for _ in 0..1 {
            // Must add variable definitions for each variable at each time step.
            smt_problem.add_variable_definitions(
                &self.state_variables,
                &self.input_variables,
                &self.actions,
                &mut builder,
            );
            smt_problem.add_assertion(&self.transition_condition, &mut builder, &mut definitions);
            builder.add_step();
        }
        // Don't forget the variable definitions at time `length`.
        smt_problem.add_variable_definitions(
            &self.state_variables,
            &self.input_variables,
            &self.actions,
            &mut builder,
        );
        smt_problem
    }

    pub fn get_property_term(&self) -> SMTProblem {
        let mut builder = self.bmc_builder();
        let mut definitions = DefinitionMaterializer::new(
            self.helper_definitions.clone(),
            builder.definition_frames().clone(),
        );
        let mut smt_problem = SMTProblem::new(&self.sorts, &self.function_definitions);
        smt_problem.add_variable_definitions(
            &self.state_variables,
            &self.input_variables,
            &self.actions,
            &mut builder,
        );
        smt_problem.add_property_assertion(
            &self.property_condition,
            &mut builder,
            &mut definitions,
        );
        smt_problem
    }

    pub fn as_commands(&self) -> Vec<Command> {
        let mut commands = self.info.clone();
        commands.extend(self.sorts.clone());
        commands.extend(self.function_definitions.clone());
        commands.extend(self.input_variables.clone());
        for variable in self.state_variables.clone() {
            commands.extend(variable.as_commands());
        }
        for action in self.actions.clone() {
            commands.extend(action.as_commands());
        }
        commands.extend(self.helper_definitions.as_commands());
        let init_command = Command::DefineFun {
            sig: FunctionDec {
                name: Symbol("init".to_string()),
                parameters: vec![],
                result: Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Bool".to_string()),
                    },
                },
            },
            term: self.initial_condition.clone(),
        };
        commands.push(init_command);
        let trans_command = Command::DefineFun {
            sig: FunctionDec {
                name: Symbol("trans".to_string()),
                parameters: vec![],
                result: Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Bool".to_string()),
                    },
                },
            },
            term: self.transition_condition.clone(),
        };
        commands.push(trans_command);
        let prop_command = Command::DefineFun {
            sig: FunctionDec {
                name: Symbol("prop".to_string()),
                parameters: vec![],
                result: Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Bool".to_string()),
                    },
                },
            },
            term: self.property_condition.clone(),
        };
        commands.push(prop_command);

        commands
    }

    pub fn print_stats(&self) {
        info!("Number of Variables: {}", self.state_variables.len());
        info!("Number of Inputs: {}", self.input_variables.len());
        info!("Number of Actions: {}", self.actions.len());
        info!("Number of Sorts: {}", self.sorts.len());
    }

    pub fn as_vmt_string(&self) -> String {
        self.as_commands()
            .iter()
            .map(|command| format!("{}", command.clone().accept(&mut SyntaxBuilder).unwrap()))
            .join("\n")
    }

    pub fn get_all_current_variable_names(&self) -> Vec<String> {
        let mut state_variable_names: Vec<String> = self
            .state_variables
            .iter()
            .map(|var| var.get_current_variable_name().clone())
            .collect();
        state_variable_names.extend(self.input_variables.iter().map(|input| match input {
            Command::DeclareFun { symbol, .. } => symbol.0.clone(),
            _ => panic!("VMT input variable must be declared with declare-fun"),
        }));
        let mut action_names: Vec<String> = self
            .actions
            .iter()
            .map(|action| action.get_current_action_name().clone())
            .collect();
        state_variable_names.append(&mut action_names);
        state_variable_names
    }

    pub fn get_next_to_current_varible_names(&self) -> HashMap<String, String> {
        self.state_variables
            .iter()
            .map(|var| {
                (
                    var.get_next_variable_name().clone(),
                    var.get_current_variable_name().clone(),
                )
            })
            .collect()
    }

    fn bmc_builder(&self) -> BMCBuilder {
        let current_variables = self.get_all_current_variable_names();
        let next_variables = self.get_next_to_current_varible_names();
        let definition_frames = DefinitionFrameInfo::new(
            &self.helper_definitions,
            &current_variables,
            &next_variables,
        );
        BMCBuilder::with_definition_frames(current_variables, next_variables, definition_frames)
    }

    #[allow(unused)]
    fn get_current_to_next_varible_names(&self) -> HashMap<String, String> {
        self.state_variables
            .iter()
            .map(|var| {
                (
                    var.get_current_variable_name().clone(),
                    var.get_next_variable_name().clone(),
                )
            })
            .collect()
    }

    pub fn add_instantiation(&mut self, term: &Term) -> bool {
        debug!("ADDED INSTANCE TO VMTModel: {}", term);
        self.initial_condition =
            self.add_instantiation_to_condition(term.clone(), self.initial_condition.clone());
        self.transition_condition =
            self.add_instantiation_to_condition(term.clone(), self.transition_condition.clone());
        true
    }

    pub fn get_parametric_sort_names(&self) -> Vec<String> {
        self.sorts
            .iter()
            .map(|sort| match sort {
                Command::DeclareSort { symbol, arity: _ } => symbol.0.clone(),
                _ => panic!("Sort in VMTModel is not of type DefineSort!: {}", sort),
            })
            .collect::<Vec<_>>()
    }

    pub fn get_state_variables(&self) -> Vec<Variable> {
        self.state_variables.clone()
    }

    pub fn get_input_variables(&self) -> Vec<Command> {
        self.input_variables.clone()
    }

    fn add_instantiation_to_condition(&self, instantiation: Term, condition: Term) -> Term {
        let (term, attributes) = match condition {
            Term::Attributes { term, attributes } => (term, attributes),
            _ => panic!("Condition is not an Attributes: {}", condition),
        };
        let mut and_terms = get_and_terms(*term);
        and_terms.push(instantiation.clone());
        Term::Attributes {
            term: Box::new(Term::Application {
                qual_identifier: crate::concrete::QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("and".to_string()),
                    },
                },
                arguments: and_terms,
            }),
            attributes,
        }
    }

    pub fn write_vmt_out(&self, filename_opt: Option<String>) {
        let filename = match filename_opt {
            Some(fname) => fname,
            None => "out.vmt".into(),
        };
        log::info!("creating: {filename}");
        let mut file = File::create(filename).unwrap();

        let _ = file.write(self.as_vmt_string().as_bytes()).unwrap();
    }

    pub fn get_function_definitions(&self) -> Vec<Command> {
        self.function_definitions.clone()
    }

    pub fn get_helper_definitions(&self) -> &DefinitionGraph {
        &self.helper_definitions
    }

    pub fn get_info(&self) -> Vec<Command> {
        self.info.clone()
    }

    pub fn get_sorts(&self) -> Vec<Command> {
        self.sorts.clone()
    }
}

#[cfg(test)]
mod test {
    #[allow(unused_imports)]
    use super::*;

    fn parse_vmt(input: &[u8]) -> Result<VMTModel, VMTError> {
        let commands = CommandStream::new(input, SyntaxBuilder, None)
            .collect::<Result<Vec<_>, concrete::Error>>()?;
        VMTModel::checked_from(commands)
    }

    #[test]
    fn finds_system_components_among_additional_definitions() {
        let input = br#"
            (set-info :source |parser regression test|)
            (set-info :category "crafted")
            (declare-fun x () Int)
            (define-fun x.next.relationship () Int (! x :next x.next))
            (declare-fun x.next () Int)
            (define-fun helper.before () Int (+ x 1))
            (define-fun init () Bool (! (= x.next.relationship 0) :init true))
            (define-fun helper.middle () Bool (= x.next x.next.relationship))
            (define-fun helper.after () Bool (>= x.next.relationship 0))
            (define-fun property () Bool (! helper.after :invar-property 0))
            (define-fun transition () Bool (! helper.middle :trans true))
            (assert true)
            (assert true)
        "#;

        let model = parse_vmt(input).expect("VMT components should be found by attribute");

        assert_eq!(model.get_info().len(), 2);
        assert_eq!(
            model
                .as_commands()
                .iter()
                .take(2)
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            vec![
                "(set-info :source |parser regression test|)",
                "(set-info :category \"crafted\")",
            ]
        );
        assert!(model.get_function_definitions().is_empty());
        assert_eq!(model.get_all_current_variable_names(), vec!["x"]);
        assert_eq!(model.get_helper_definitions().len(), 3);
        assert_eq!(
            model
                .get_helper_definitions()
                .iter()
                .map(|definition| definition.name())
                .collect::<Vec<_>>(),
            vec!["helper.before", "helper.middle", "helper.after"]
        );
        assert_eq!(
            model
                .get_helper_definitions()
                .get("helper.middle")
                .unwrap()
                .body()
                .to_string(),
            "(= x.next x)"
        );
        assert_eq!(
            model.get_initial_condition_for_yardbird().to_string(),
            "(= x 0)"
        );
        assert_eq!(
            model.get_property_for_yardbird().to_string(),
            "helper.after"
        );
        assert_eq!(
            model.get_trans_condition_for_yardbird().to_string(),
            "helper.middle"
        );
        assert_eq!(
            model
                .as_commands()
                .iter()
                .filter(|command| command.to_string() == "(declare-fun x.next () Int)")
                .count(),
            1
        );
    }

    #[test]
    fn implicitly_declares_an_undeclared_next_state_variable() {
        let input = br#"
            (declare-fun x () Int)
            (define-fun x.next.relationship () Int (! x :next x.next))
            (define-fun init () Bool (! (= x 0) :init true))
            (define-fun transition () Bool (! (= x.next x) :trans true))
            (define-fun property () Bool (! (>= x 0) :invar-property 0))
        "#;

        let model = parse_vmt(input).expect("the next-state declaration should be inferred");

        assert_eq!(
            model.get_next_to_current_varible_names(),
            HashMap::from([("x.next".to_string(), "x".to_string())])
        );
        assert!(model
            .as_commands()
            .iter()
            .any(|command| command.to_string() == "(declare-fun x.next () Int)"));
    }

    #[test]
    fn one_definition_can_describe_both_a_state_pair_and_the_property() {
        let input = br#"
            (declare-fun ok () Bool)
            (declare-fun ok.next () Bool)
            (define-fun init () Bool (! (not ok) :init true))
            (define-fun transition () Bool (! (= ok.next ok) :trans true))
            (define-fun property-and-next () Bool
                (! ok :next ok.next :invar-property 0))
        "#;

        let model = parse_vmt(input).expect("all metadata roles should be processed");

        assert_eq!(
            model.get_next_to_current_varible_names(),
            HashMap::from([("ok.next".to_string(), "ok".to_string())])
        );
        assert_eq!(model.get_property_for_yardbird().to_string(), "ok");

        let reparsed = VMTModel::checked_from(model.as_commands())
            .expect("serialized metadata roles should remain independently parseable");
        assert_eq!(
            reparsed.get_next_to_current_varible_names(),
            HashMap::from([("ok.next".to_string(), "ok".to_string())])
        );
        assert_eq!(reparsed.get_property_for_yardbird().to_string(), "ok");
    }

    #[test]
    fn unpaired_declarations_are_fresh_inputs_at_each_frame() {
        let input = br#"
            (declare-fun x () Int)
            (declare-fun x.next () Int)
            (declare-fun input () Int)
            (define-fun x.relationship () Int (! x :next x.next))
            (define-fun init () Bool (! (= x 0) :init true))
            (define-fun transition () Bool (! (= x.next input) :trans true))
            (define-fun property () Bool (! (>= x 0) :invar-property 0))
        "#;

        let model = parse_vmt(input).unwrap();
        let bmc = model.unroll(1).to_bmc();

        assert_eq!(model.get_all_current_variable_names(), vec!["x", "input"]);
        assert!(bmc.contains("(declare-fun input@0 () Int)"));
        assert!(bmc.contains("(declare-fun input@1 () Int)"));
        assert!(bmc.contains("(= x@1 input@0)"));
    }

    #[test]
    fn reports_a_missing_system_component() {
        let input = br#"
            (define-fun init () Bool (! true :init true))
            (define-fun transition () Bool (! true :trans true))
            (define-fun helper () Bool true)
        "#;

        assert!(matches!(
            parse_vmt(input),
            Err(VMTError::MissingSystemComponent("invar-property"))
        ));
    }

    #[test]
    fn reports_a_duplicate_system_component() {
        let input = br#"
            (define-fun init.one () Bool (! true :init true))
            (define-fun transition () Bool (! true :trans true))
            (define-fun property () Bool (! true :invar-property 0))
            (define-fun init.two () Bool (! false :init true))
        "#;

        assert!(matches!(
            parse_vmt(input),
            Err(VMTError::DuplicateSystemComponent("init"))
        ));
    }

    #[test]
    fn reports_cyclic_zero_argument_definitions() {
        let input = br#"
            (define-fun left () Int right)
            (define-fun right () Int left)
            (define-fun init () Bool (! (= left 0) :init true))
            (define-fun transition () Bool (! true :trans true))
            (define-fun property () Bool (! true :invar-property 0))
        "#;

        assert!(matches!(
            parse_vmt(input),
            Err(VMTError::CyclicDefinition(name)) if name == "left"
        ));
    }

    #[test]
    fn unrolls_reachable_helpers_once_per_frame_without_tree_expansion() {
        let input = br#"
            (declare-fun x () Int)
            (define-fun x.relationship () Int (! x :next x.next))
            (define-fun one () Int 1)
            (define-fun inc () Int (+ x one))
            (define-fun twice-inc () Int (+ inc inc))
            (define-fun init () Bool (! (= x 0) :init true))
            (define-fun transition () Bool (! (= x.next inc) :trans true))
            (define-fun property () Bool (! (<= twice-inc 20) :invar-property 0))
        "#;

        let model = parse_vmt(input).unwrap();
        let bmc = model.unroll(2).to_bmc();

        assert_eq!(bmc.matches("(declare-fun one () Int)").count(), 1);
        for frame in 0..=2 {
            assert_eq!(
                bmc.matches(&format!("(declare-fun inc@{frame} () Int)"))
                    .count(),
                1
            );
        }
        assert_eq!(bmc.matches("(declare-fun twice-inc@2 () Int)").count(), 1);
        assert!(bmc.contains("(= inc@2 (+ x@2 one))"));
        assert!(bmc.contains("(= twice-inc@2 (+ inc@2 inc@2))"));
        assert!(!bmc.contains("(+ (+ x@2 one) (+ x@2 one))"));
    }

    #[test]
    fn helper_temporal_footprints_include_transitive_next_state_dependencies() {
        let input = br#"
            (declare-fun x () Int)
            (define-fun x.relationship () Int (! x :next x.next))
            (define-fun next-value () Int (+ x.next 1))
            (define-fun init () Bool (! true :init true))
            (define-fun transition () Bool (! (= x.next next-value) :trans true))
            (define-fun property () Bool (! true :invar-property 0))
        "#;

        let model = parse_vmt(input).unwrap();
        let current = model.get_all_current_variable_names();
        let next = model.get_next_to_current_varible_names();
        let frames = DefinitionFrameInfo::new(model.get_helper_definitions(), &current, &next);
        assert_eq!(
            frames
                .offsets("next-value")
                .unwrap()
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            vec![1]
        );

        let instance = UnquantifiedInstantiator::rewrite_with_definitions(
            "next-value@4".parse().unwrap(),
            frames,
        )
        .unwrap();
        assert_eq!(instance.width(), 1);
        assert_eq!(instance.get_term().to_string(), "next-value+0");

        let mut builder = model.bmc_builder();
        builder.set_depth(5);
        builder.set_width(instance.width());
        assert_eq!(instance.rewrite(&mut builder).to_string(), "next-value@4");
    }

    #[test]
    fn array_abstraction_rewrites_helper_result_sorts_and_bodies() {
        let input = br#"
            (declare-fun a () (Array Int Int))
            (define-fun a.relationship () (Array Int Int) (! a :next a.next))
            (define-fun updated () (Array Int Int) (store a 0 1))
            (define-fun read-updated () Int (select updated 0))
            (define-fun direct-read () Int (select (store a 0 1) 0))
            (define-fun init () Bool (! true :init true))
            (define-fun transition () Bool (! (= a.next updated) :trans true))
            (define-fun property () Bool (! (= read-updated 1) :invar-property 0))
        "#;

        let model = parse_vmt(input).unwrap();
        let (abstracted_without_preprocessing, _) = model.abstract_array_theory();
        assert_eq!(
            abstracted_without_preprocessing
                .get_helper_definitions()
                .get("direct-read")
                .unwrap()
                .body()
                .to_string(),
            "(Read_Int_Int (Write_Int_Int a 0 1) 0)"
        );

        let (abstracted, types) = model.abstract_array_theory_with_preprocessing(true);
        assert_eq!(types, vec![("Int".to_string(), "Int".to_string())]);

        let updated = abstracted.get_helper_definitions().get("updated").unwrap();
        assert_eq!(updated.sort().to_string(), "Array_Int_Int");
        assert_eq!(updated.body().to_string(), "(Write_Int_Int a 0 1)");
        assert_eq!(
            abstracted
                .get_helper_definitions()
                .get("read-updated")
                .unwrap()
                .body()
                .to_string(),
            "(Read_Int_Int updated 0)"
        );
        assert_eq!(
            abstracted
                .get_helper_definitions()
                .get("direct-read")
                .unwrap()
                .body()
                .to_string(),
            "1"
        );
    }

    #[test]
    fn rejects_nontrailing_or_meaningful_assertions() {
        let nontrailing = br#"
            (assert true)
            (define-fun init () Bool (! true :init true))
            (define-fun transition () Bool (! true :trans true))
            (define-fun property () Bool (! true :invar-property 0))
        "#;
        let meaningful = br#"
            (define-fun init () Bool (! true :init true))
            (define-fun transition () Bool (! true :trans true))
            (define-fun property () Bool (! true :invar-property 0))
            (assert false)
        "#;

        assert!(matches!(
            parse_vmt(nontrailing),
            Err(VMTError::UnknownCommand(_))
        ));
        assert!(matches!(
            parse_vmt(meaningful),
            Err(VMTError::UnknownCommand(_))
        ));
    }

    #[test]
    fn test_double_abstract() {
        let vmt_model = VMTModel::from_path("./examples/array_copy.vmt").unwrap();
        let (abstracted_model, _types) = vmt_model.abstract_array_theory();
        let (abstracted_abstracted_model, _types) = abstracted_model.abstract_array_theory();

        assert_eq!(
            abstracted_model.as_vmt_string(),
            abstracted_abstracted_model.as_vmt_string(),
        );
    }
}
