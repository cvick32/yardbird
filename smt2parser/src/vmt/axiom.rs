use crate::concrete::{Command, FunctionDec, Identifier, Sort, Symbol, Term};

#[derive(Clone, Debug)]
pub struct Axiom {
    pub _axiom: Term,
}

impl Axiom {
    pub(crate) fn as_command(&self) -> Command {
        Command::Assert {
            term: self._axiom.clone(),
        }
    }

    pub(crate) fn _as_commands(&self) -> Vec<Command> {
        let dd = FunctionDec {
            name: Symbol("axiom".into()),
            parameters: vec![],
            result: Sort::Simple {
                identifier: Identifier::Simple {
                    symbol: Symbol("Bool".into()),
                },
            },
        };
        let command = Command::DefineFun {
            sig: dd,
            term: self._axiom.clone(),
        };
        vec![command]
    }
}
