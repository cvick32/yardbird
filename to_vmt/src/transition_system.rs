use smt2parser::{
    get_command_from_command_string,
    vmt::{VMTModel, NEXT_VARIABLE_NAME},
};

use crate::FunctionArgument;

pub fn to_vmt_model(
    variables: Vec<FunctionArgument>,
    initial_condition: Vec<String>,
    loop_conditions: Vec<Vec<String>>,
    property_condition: Vec<String>,
) -> VMTModel {
    let mut full_commands = vec![];

    // Add all the variables as commands
    for variable in &variables {
        full_commands.extend(variable.to_commands());
    }
    // Add the initial condition as a command
    let initial = format!(
        "(define-fun initial-condition () Bool (! (and {}) :init true))",
        initial_condition.join(" ")
    );
    full_commands.push(get_command_from_command_string(initial.as_bytes()));

    // Add the transitions associated with each loop
    // TODO: extend to handling 2 loops
    let mut transition_string = loop_conditions[0].clone();

    for variable in &variables {
        // If the variable is immutable, we need to add that fact in the
        // transition relation.
        if !variable.is_mutable {
            transition_string.push(format!(
                "(= {} {}_{})",
                variable.vmt_name, variable.vmt_name, NEXT_VARIABLE_NAME
            ));
        }
    }

    let transition = format!(
        "(define-fun transition-condition () Bool (! (and {}) :trans true))",
        transition_string.join(" ")
    );
    full_commands.push(get_command_from_command_string(transition.as_bytes()));

    let (pre_conditions, property) = property_condition.split_at(property_condition.len() - 1);

    let property_command = format!(
        "(define-fun property-condition () Bool (! (=> (and {}) {}) :invar-property 0))",
        pre_conditions.join(" "),
        property[0]
    );
    full_commands.push(get_command_from_command_string(property_command.as_bytes()));

    VMTModel::checked_from(full_commands).unwrap()
}
