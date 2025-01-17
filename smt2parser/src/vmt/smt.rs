use crate::{
    concrete::{Command, Term},
    let_extract::LetExtract,
    vmt::smtinterpol_utils::{
        assert_negation, assert_negation_interpolant, assert_term, assert_term_interpolant,
        get_interpolant_command, SMT_INTERPOL_OPTIONS,
    },
};

use super::{
    action::Action, bmc::BMCBuilder, non_boolean_subterms::NonBooleanSubterms,
    reads_and_write::ReadsAndWrites, variable::Variable,
};

#[derive(Default, Debug, Clone)]
pub struct SMTProblem {
    sorts: Vec<Command>,
    variable_definitions: Vec<Command>,
    function_definitions: Vec<Command>,
    init_and_trans_assertions: Vec<Term>,
    property_assertion: Option<Term>,
}

impl SMTProblem {
    pub fn new(sorts: &[Command], function_definitions: &[Command]) -> Self {
        Self {
            sorts: sorts.to_vec(),
            variable_definitions: vec![],
            function_definitions: function_definitions.to_vec(),
            init_and_trans_assertions: vec![],
            property_assertion: None,
        }
    }

    pub fn init_and_trans_length(&self) -> usize {
        self.init_and_trans_assertions.len()
    }

    pub fn get_variable_definitions(&self) -> Vec<Command> {
        self.variable_definitions.clone()
    }

    pub fn get_function_definitions(&self) -> Vec<Command> {
        self.function_definitions.clone()
    }

    pub fn add_assertion(&mut self, condition: &Term, mut builder: BMCBuilder) {
        let mut let_extract = LetExtract::default();
        let no_let_condition = condition
            .clone()
            .accept_term_visitor(&mut let_extract)
            .unwrap();
        let rewritten_condition = match no_let_condition {
            Term::Attributes {
                term,
                attributes: _,
            } => term.clone().accept(&mut builder).unwrap(),
            _ => panic!(
                "{}",
                "Assertion must be a Term::Atrributes! One of {{init, trans, invar-prop}}"
            ),
        };
        self.init_and_trans_assertions.push(rewritten_condition);
    }

    /// Need to assert the negation of the property given in the VMTModel for BMC.
    pub fn add_property_assertion(&mut self, condition: &Term, mut builder: BMCBuilder) {
        let mut let_extract = LetExtract::default();
        let no_let_condition = condition
            .clone()
            .accept_term_visitor(&mut let_extract)
            .unwrap();
        let rewritten_property = match no_let_condition {
            Term::Attributes {
                term,
                attributes: _,
            } => term.clone().accept(&mut builder).unwrap(),
            _ => panic!(
                "{}",
                "Assertion must be a Term::Atrributes! One of {{init, trans, invar-prop}}"
            ),
        };
        self.property_assertion = Some(rewritten_property);
    }

    pub fn add_variable_definitions(
        &mut self,
        state_variables: &Vec<Variable>,
        actions: &Vec<Action>,
        mut builder: BMCBuilder,
    ) {
        for state_variable in state_variables {
            let definition_at_time = state_variable.current.clone().accept(&mut builder).unwrap();
            self.variable_definitions.push(definition_at_time);
        }
        for action in actions {
            let action_at_time = action.action.clone().accept(&mut builder).unwrap();
            self.variable_definitions.push(action_at_time);
        }
    }

    pub fn get_assert_terms(&self) -> Vec<Term> {
        let mut assert_terms = self.init_and_trans_assertions.clone();
        if self.property_assertion.is_some() {
            assert_terms.push(self.property_assertion.clone().unwrap())
        }
        assert_terms
    }

    pub fn to_bmc(&self) -> String {
        let sort_names = self
            .sorts
            .iter()
            .map(|sort| sort.to_string())
            .collect::<Vec<String>>()
            .join("\n");
        let function_definitions = self
            .function_definitions
            .iter()
            .map(|fd| fd.to_string())
            .collect::<Vec<String>>()
            .join("\n");
        let defs = self
            .variable_definitions
            .iter()
            .map(|def| def.to_string())
            .collect::<Vec<String>>()
            .join("\n");
        let init_and_trans_asserts = self
            .init_and_trans_assertions
            .iter()
            .map(assert_term)
            .collect::<Vec<String>>()
            .join("\n");
        let property_assert = match &self.property_assertion {
            Some(prop) => assert_negation(prop),
            None => String::new(),
        };
        format!(
            "{}\n{}\n{}\n{}\n{}",
            sort_names, function_definitions, defs, init_and_trans_asserts, property_assert
        )
    }

    pub fn get_property_subterms(&self) -> Vec<String> {
        let mut subterms = NonBooleanSubterms::default();
        let prop = self.property_assertion.clone().unwrap();
        let _ = prop.accept_term_visitor(&mut subterms);
        subterms
            .subterms
            .iter()
            .map(|term| term.to_string())
            .collect::<Vec<_>>()
    }

    pub fn get_transition_system_subterms(&self) -> Vec<String> {
        let mut subterms = NonBooleanSubterms::default();
        for trans_assert in &self.init_and_trans_assertions {
            let _ = trans_assert.clone().accept_term_visitor(&mut subterms);
        }
        subterms
            .subterms
            .iter()
            .map(|term| term.to_string())
            .collect::<Vec<_>>()
    }

    pub fn get_all_subterms(&self) -> Vec<Term> {
        let mut subterms = NonBooleanSubterms::default();
        for trans_assert in &self.init_and_trans_assertions {
            let _ = trans_assert.clone().accept_term_visitor(&mut subterms);
        }
        let prop = self.property_assertion.clone().unwrap();
        let _ = prop.accept_term_visitor(&mut subterms);
        subterms.subterms.into_iter().collect::<Vec<_>>()
    }

    pub fn get_reads_and_writes(&self) -> ReadsAndWrites {
        let mut reads_and_writes = ReadsAndWrites::default();
        for trans_assert in &self.init_and_trans_assertions {
            _ = trans_assert
                .clone()
                .accept_term_visitor(&mut reads_and_writes);
        }
        reads_and_writes
    }

    pub fn to_smtinterpol(&self) -> String {
        let sort_names = self
            .sorts
            .iter()
            .map(|sort| sort.to_string())
            .collect::<Vec<String>>()
            .join("\n");
        let function_definitions = self
            .function_definitions
            .iter()
            .map(|fd| fd.to_string())
            .collect::<Vec<String>>()
            .join("\n");
        let defs = self
            .variable_definitions
            .iter()
            .map(|def| def.to_string())
            .collect::<Vec<String>>()
            .join("\n");
        let init_and_trans_asserts = self
            .init_and_trans_assertions
            .iter()
            .enumerate()
            .map(|(i, assertion)| assert_term_interpolant(i, assertion))
            .collect::<Vec<String>>()
            .join("\n");
        let property_assert = match &self.property_assertion {
            Some(prop) => assert_negation_interpolant(self.init_and_trans_length(), prop),
            None => String::new(),
        };
        let interpolant_command = get_interpolant_command(self.init_and_trans_length());
        format!(
            "{}\n{}\n{}\n{}\n{}\n{}\n{}",
            SMT_INTERPOL_OPTIONS,
            sort_names,
            function_definitions,
            defs,
            init_and_trans_asserts,
            property_assert,
            interpolant_command
        )
    }
}
