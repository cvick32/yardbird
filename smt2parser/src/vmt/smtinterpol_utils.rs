use itertools::Itertools;
use num::range;

use crate::{concrete::Term, vmt::canonicalize_boolean::CanonicalizeBooleanFunctions};

pub static SMT_INTERPOL_OPTIONS: &str = "(set-option :print-success false)\n(set-option :produce-interpolants true)\n(set-logic QF_UFLIA)";

static INTERPOLANT_NAMES: [&str; 26] = [
    "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S",
    "T", "U", "V", "W", "X", "Y", "Z",
];

pub fn assert_term(assertion: &Term) -> String {
    format!("(assert {})", assertion)
}

pub fn assert_negation(assertion: &Term) -> String {
    format!("(assert (not {}))", assertion)
}

pub fn assert_term_interpolant(i: usize, assertion: &Term) -> String {
    let mut canonicalize_and = CanonicalizeBooleanFunctions {};
    let canonical = assertion
        .clone()
        .accept_term_visitor(&mut canonicalize_and)
        .unwrap();
    format!(
        "(assert (! {} :named {}))",
        canonical,
        get_interpolant_name(i)
    )
}

pub fn assert_negation_interpolant(i: usize, assertion: &Term) -> String {
    let mut canonicalize_and = CanonicalizeBooleanFunctions {};
    let canonical = assertion
        .clone()
        .accept_term_visitor(&mut canonicalize_and)
        .unwrap();
    format!(
        "(assert (! (not {}) :named {}))",
        canonical,
        get_interpolant_name(i)
    )
}

pub fn get_interpolant_command(i: usize) -> String {
    format!("(check-sat)\n{}", get_interpolant_names(i))
}

fn get_interpolant_names(i: usize) -> String {
    let names: String = range(0, i + 1).map(get_interpolant_name).join(" ");
    format!("(get-interpolants {names})")
}

fn get_interpolant_name(i: usize) -> String {
    if i <= 25 {
        INTERPOLANT_NAMES[i].into()
    } else {
        log::info!("{}", u8::MAX);
        let rest = i - 26;
        INTERPOLANT_NAMES[0].to_owned() + &get_interpolant_name(rest)
    }
}

mod tests {
    #[allow(unused_imports)]
    use super::*;

    #[test]
    fn test_interpolant_name() {
        assert_eq!(get_interpolant_name(0), "A");
        assert_eq!(get_interpolant_name(10), "K");
        assert_eq!(get_interpolant_name(26), "AA");
        assert_eq!(get_interpolant_name(27), "AB");
        assert_eq!(get_interpolant_name(52), "AAA");
    }
}
