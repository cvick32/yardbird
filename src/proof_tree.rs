use log::info;
use z3::ast::{Ast, Dynamic};

/// The idea of this is to parse the Z3 proof tree and count up how many
/// array instantiations are in it. This is to measure the
pub struct ProofTree {
    _ast: Dynamic,
    _array_axiom_instantiations: Vec<Dynamic>,
}

impl ProofTree {
    pub fn new(ast: impl Ast) -> Self {
        let mut to_process = ast.children();

        while let Some(rule) = to_process.pop() {
            if rule.decl().kind() == z3::DeclKind::PR_TH_LEMMA {
                info!("{:?}: {}", rule.decl().kind(), rule);
            }
            if !rule.children().is_empty() {
                to_process.extend_from_slice(&rule.children());
            }
        }
        let first = ast.children()[0].clone();
        ProofTree {
            _ast: first,
            _array_axiom_instantiations: vec![],
        }
    }
}
