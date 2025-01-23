use crate::interpolant::Interpolant;
use smt2parser::{get_term_from_term_string, let_extract::LetExtract, vmt::smt::SMTProblem};
use std::{
    fs::File,
    io::{Error, Write},
    process::Command,
};

static INTERPOLANT_FILENAME: &str = "interpolant-out.smt2";

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
