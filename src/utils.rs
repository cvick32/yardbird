use smt2parser::{
    get_term_from_assert_command_string, let_extract::LetExtract, vmt::smt::SMTProblem,
};
use std::{
    fs::File, io::{Error, Write}, process::Command
};

static INTERPOLANT_FILENAME: &str = "interpolant-out.smt2";

pub fn run_smtinterpol(smt_problem: SMTProblem) -> Result<Vec<String>, Error> {
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
    let dd = interpolants.clone();
    // Have to add `and` to the interpolant to make it valid smt2
    interpolants.insert_str(1, "and ");
    // Format it to `assert` call so smt2parser can handle it.
    let term = get_term_from_assert_command_string(format!("(assert {})", interpolants).as_bytes());
    let mut let_extract = LetExtract::default();
    let sequent_interpolant = term.clone().accept_term_visitor(&mut let_extract).unwrap();
    // Interpolants will now be the arguments to the `and` term created above. 
    let _interpolants = match sequent_interpolant {
        smt2parser::concrete::Term::Application { qual_identifier: _, arguments } => arguments,
        _ => panic!("Sequent interpolant is not `and` application.")
    };
    let mut i = 0;
    println!("-----------------------{}---------------------------", interpolants.len());
    for interp in interpolants {
        println!("{i}: {interp}");
        i += 1;
    }

    Ok(vec![dd])
}
