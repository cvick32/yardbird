use crate::concrete::Command;

#[derive(Clone, Debug)]
pub struct Variable {
    pub current: Command,
    pub next: Command,
    pub relationship: Command,
}

impl Variable {
    pub fn get_current_variable_name(&self) -> &String {
        match &self.current {
            Command::DeclareFun {
                symbol,
                parameters: _,
                sort: _,
            } => &symbol.0,
            _ => panic!("Variable's current Command must be DeclareFun."),
        }
    }

    pub fn get_next_variable_name(&self) -> &String {
        match &self.next {
            Command::DeclareFun {
                symbol,
                parameters: _,
                sort: _,
            } => &symbol.0,
            _ => panic!("Variable's next Command must be DeclareFun."),
        }
    }

    pub fn get_sort_name(&self) -> String {
        match &self.current {
            Command::DeclareFun {
                symbol: _,
                parameters: _,
                sort,
            } => match sort {
                crate::concrete::Sort::Simple { identifier } => match identifier {
                    crate::concrete::Identifier::Simple { symbol } => symbol.0.clone(),
                    crate::concrete::Identifier::Indexed { symbol, indices } => {
                        let indices_str = indices
                            .iter()
                            .map(|index| index.to_string())
                            .collect::<Vec<String>>()
                            .join(" ");
                        format!("({} {})", symbol.0, indices_str)
                    }
                },
                crate::concrete::Sort::Parameterized {
                    identifier,
                    parameters,
                } => match identifier {
                    crate::concrete::Identifier::Simple { symbol } => symbol.0.clone(),
                    crate::concrete::Identifier::Indexed { symbol, indices } => {
                        let param_str = parameters
                            .iter()
                            .map(|index| index.to_string())
                            .collect::<Vec<String>>()
                            .join(" ");
                        let indices_str = indices
                            .iter()
                            .map(|index| index.to_string())
                            .collect::<Vec<String>>()
                            .join(" ");
                        format!("({} ({}) {})", symbol.0, param_str, indices_str)
                    }
                },
            },
            _ => panic!("Variable's current Command must be DeclareFun."),
        }
    }

    pub(crate) fn as_commands(&self) -> Vec<Command> {
        vec![
            self.current.clone(),
            self.next.clone(),
            self.relationship.clone(),
        ]
    }
}
