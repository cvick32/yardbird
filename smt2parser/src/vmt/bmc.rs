use std::collections::HashMap;

use crate::concrete::{Symbol, SyntaxBuilder};

#[derive(Clone)]
pub struct BMCBuilder {
    pub visitor: SyntaxBuilder,
    pub current_variables: Vec<String>,
    pub next_variables: HashMap<String, String>,
    pub step: u8,
}

impl BMCBuilder {
    pub fn new(current_variables: Vec<String>, next_variables: HashMap<String, String>) -> Self {
        BMCBuilder {
            visitor: SyntaxBuilder,
            current_variables,
            next_variables,
            step: 0,
        }
    }

    pub fn set_step(&mut self, depth: u8) {
        self.step = depth;
    }

    pub fn add_step(&mut self) {
        self.step += 1;
    }
}

impl crate::rewriter::Rewriter for BMCBuilder {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
        if self.current_variables.contains(&s.0) {
            Ok(Symbol(format!("{}@{}", s.0, &self.step)))
        } else if self.next_variables.contains_key(&s.0) {
            let next = self.step + 1;
            let current_variable_name = self.next_variables.get(&s.0).unwrap();
            Ok(Symbol(format!(
                "{}@{}",
                current_variable_name,
                &next.to_string()
            )))
        } else {
            Ok(s)
        }
    }
}
