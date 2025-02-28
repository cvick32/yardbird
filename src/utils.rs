use crate::interpolant::Interpolant;
use smt2parser::{get_term_from_term_string, let_extract::LetExtract, vmt::smt::SMTProblem};
use std::{
    fs::File,
    io::{Error, Write},
    process::Command,
};
use z3::ast::{Ast, Dynamic};

static INTERPOLANT_FILENAME: &str = "interpolant-out.smt2";

pub fn run_command(cmd: &str, args: &[&str]) -> Result<String, String> {
    let output = Command::new(cmd)
        .args(args)
        .output()
        .map_err(|e| format!("Failed to execute command: {}", e))?;

    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).trim().to_string())
    }
}

pub fn run_smtinterpol(smt_problem: &SMTProblem) -> Result<Vec<Interpolant>, Error> {
    let interpolant_problem = smt_problem.to_smtinterpol();
    let mut temp_file = File::create(INTERPOLANT_FILENAME)?;
    writeln!(temp_file, "{interpolant_problem}")?;
    let interp_out = Command::new("java")
        .arg("-jar")
        .arg("./tools/smtinterpol-2.5-1386-gcca67e02.jar")
        .arg("-w") // Only output interpolants.
        .arg(INTERPOLANT_FILENAME)
        .output()?;

    let string_stdout = String::from_utf8(interp_out.stdout).unwrap();
    let stdout = string_stdout
        .split("\n")
        .map(|s| s.to_string())
        .collect::<Vec<_>>();

    // First element should always be 'unsat' from (check-sat) call.
    assert_eq!(stdout[0], "unsat");
    // Second element is the sequent interpolant.
    let mut interpolants = stdout[1].clone();
    // Have to add `and` to the interpolant to make it valid smt2
    interpolants.insert_str(1, "and ");
    // Format it to `assert` call so smt2parser can handle it.
    let term = get_term_from_term_string(&interpolants);
    let sequent_interpolant = LetExtract::substitute(term.clone());
    // Interpolants will now be the arguments to the `and` term created above.
    log::debug!("----------------------------------------");
    let interpolants = match sequent_interpolant {
        smt2parser::concrete::Term::Application {
            qual_identifier: _,
            arguments,
        } => arguments
            .iter()
            .enumerate()
            .map(|(interpolant_number, term)| Interpolant::from(term, interpolant_number))
            .collect(),
        _ => panic!("Sequent interpolant is not `and` application."),
    };
    Ok(interpolants)
}

pub fn _interpolant_formula_to_2_d_points(
    interpolant_formula: &Dynamic<'_>,
    x: f32,
    y: f32,
) -> Vec<(f32, f32)> {
    if !interpolant_formula.is_app() {
        vec![(x + 1.0, y)]
    } else {
        let args = interpolant_formula.children();
        let mut counter = y;
        args.iter()
            .flat_map(|arg| {
                counter += 1.0;
                _interpolant_formula_to_2_d_points(arg, x, counter)
            })
            .collect::<Vec<(f32, f32)>>()
    }
}
