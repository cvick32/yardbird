use egg::*;
use log::info;
use smt2parser::{concrete::Term, get_term_from_term_string};
use std::fmt::Debug;

pub struct Interpolant {
    pub _original_term: Term,
    pub simplified_term: Term,
    pub interpolant_number: usize,
}

impl Interpolant {
    pub fn from(term: &Term, interpolant_number: usize) -> Self {
        let simplified = simplify_smtinterpol_interpolant(term.to_string());
        Interpolant {
            _original_term: term.clone(),
            interpolant_number,
            simplified_term: get_term_from_term_string(&simplified),
        }
    }
}

impl Debug for Interpolant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(format!("{}: {}", self.interpolant_number, self.simplified_term).as_str())
    }
}

fn simplify_smtinterpol_interpolant(interpolant: String) -> String {
    // parse the expression, the type annotation tells it which Language to use
    let expr: RecExpr<ArrayInterpolantLanguage> = interpolant.parse().unwrap();

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    let runner = Runner::default()
        .with_expr(&expr)
        .run(&interpolant_rewrites());

    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_, best) = extractor.find_best(root);
    info!(
        "Reduced SMTInterpol interpolant length from {} to {} -- {}%",
        interpolant.len(),
        best.to_string().len(),
        ((best.to_string().len() as f64 - interpolant.len() as f64) / interpolant.len() as f64)
            * 100.0
    );
    best.to_string()
}

define_language! {
    pub enum ArrayInterpolantLanguage {
        Num(i64),
        "ConstArr-Int-Int" = ConstArr([Id; 1]),
        "Write-Int-Int" = Write([Id; 3]),
        "Read-Int-Int" = Read([Id; 2]),
        "and" = And(Box<[Id]>),
        "not" = Not(Id),
        "or" = Or(Box<[Id]>),
        "=>" = Implies([Id; 2]),
        "=" = Eq([Id; 2]),
        ">=" = Geq([Id; 2]),
        ">" = Gt([Id; 2]),
        "<=" = Leq([Id; 2]),
        "<" = Lt([Id; 2]),
        "mod" = Mod([Id; 2]),
        "+" = Plus(Box<[Id]>),
        "-" = Negate(Box<[Id]>),
        "*" = Times(Box<[Id]>),
        "ite" = Ite([Id; 3]),
        Symbol(Symbol),
    }
}

/// This rewriter is tuned to the interpolants you get out of SMTInterpol.
fn interpolant_rewrites() -> Vec<Rewrite<ArrayInterpolantLanguage, ()>> {
    vec![
        rewrite!("add-0"; "(+ ?a 0)" => "?a"),
        rewrite!("mul-0"; "(* ?a 0)" => "0"),
        rewrite!("mul-1"; "(* ?a 1)" => "?a"),
        rewrite!("mul-neg-is-plus-one"; "(= (+ ?a (* (- 1) ?b) 1) 0))" => "(= ?b (+ 1 ?a))"),
        rewrite!("def-eq"; "(= ?a ?a)" => "true"),
        rewrite!("def-lt"; "(< ?a ?a)" => "false"),
        rewrite!("def-gt"; "(> ?a ?a)" => "false"),
        rewrite!("def-lte"; "(<= ?a ?a)" => "true"),
        rewrite!("def-gte"; "(>= ?a ?a)" => "true"),
        rewrite!("constant-array"; "(Read-Int-Int (ConstArr-Int-Int ?a) ?b)" => "?a"),
        rewrite!("read-after-write"; "(Read-Int-Int (Write-Int-Int ?a ?idx ?val) ?idx)" => "?val"),
        rewrite!(
            "write-does-not-overwrite"; "(Read-Int-Int (Write-Int-Int ?a ?idx ?val) ?c)" => "(Read-Int-Int ?a ?c)" if not_equal("?idx", "?c")
        ),
    ]
}

fn not_equal(
    index_0: &'static str,
    index_1: &'static str,
) -> impl Fn(&mut EGraph<ArrayInterpolantLanguage, ()>, Id, &Subst) -> bool {
    let var_0 = index_0.parse().unwrap();
    let var_1 = index_1.parse().unwrap();
    move |egraph, _, subst| egraph.find(subst[var_0]) != egraph.find(subst[var_1])
}
