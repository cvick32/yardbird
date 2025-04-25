use log::info;
use z3::ast::{Ast, Dynamic};

/// The idea of this is to parse the Z3 proof tree and count up how many
/// array instantiations are in it. This is to measure the
pub struct ProofTree<'ctx> {
    _ast: Dynamic<'ctx>,
    _array_axiom_instantiations: Vec<Dynamic<'ctx>>,
}

impl<'ctx> ProofTree<'ctx> {
    pub fn new(ast: impl Ast<'ctx>) -> Self {
        let mut to_process = ast.children();

        while let Some(rule) = to_process.pop() {
            if rule.decl().kind() == z3::DeclKind::PR_TH_LEMMA {
                info!("{:?}: {}", rule.decl().kind(), rule.to_string());
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
