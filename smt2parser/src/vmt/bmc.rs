use std::collections::HashMap;

use crate::concrete::{Symbol, SyntaxBuilder};

#[derive(Clone)]
pub struct BMCBuilder {
    pub visitor: SyntaxBuilder,
    pub current_variables: Vec<String>,
    pub next_variables: HashMap<String, String>,
    pub depth: u8,
}

impl BMCBuilder {
    pub fn new(current_variables: Vec<String>, next_variables: HashMap<String, String>) -> Self {
        BMCBuilder {
            visitor: SyntaxBuilder,
            current_variables,
            next_variables,
            depth: 0,
        }
    }

    pub fn set_depth(&mut self, depth: u8) {
        self.depth = depth;
    }

    pub fn add_step(&mut self) {
        self.depth += 1;
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
            Ok(Symbol(format!("{}@{}", s.0, &self.depth)))
        } else if self.next_variables.contains_key(&s.0) {
            let next = self.depth + 1;
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
