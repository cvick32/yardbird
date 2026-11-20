//! Ground-term admission for interactive clients. Inference of an output sort
//! alone is insufficient at this boundary: every argument and arity is checked.
use super::snapshot::{CatalogueTerm, InstantiationSnapshot};
use crate::terms::language::TermLanguage;
use smt2parser::{
    concrete::{Command, Constant, Sort, Term},
    visitors::Identifier,
};
use std::collections::{BTreeMap, HashMap};

type Signatures = HashMap<String, (Vec<Sort>, Sort)>;

pub(crate) fn parse(text: &str) -> anyhow::Result<Term> {
    // Bound recursive parser work before constructing a potentially deep AST.
    anyhow::ensure!(
        text.bytes().filter(|b| *b == b'(').count() <= 256,
        "term syntax budget exceeded"
    );
    let wrapped = format!("(assert {text})");
    let commands = smt2parser::CommandStream::new(
        wrapped.as_bytes(),
        smt2parser::concrete::SyntaxBuilder,
        None,
    )
    .collect::<Result<Vec<_>, _>>()?;
    match commands.as_slice() {
        [Command::Assert { term }] => Ok(term.clone()),
        _ => anyhow::bail!("expected exactly one term, not commands"),
    }
}

impl InstantiationSnapshot {
    pub(super) fn parse_ground_binding(
        &self,
        text: &str,
        work: &mut usize,
    ) -> anyhow::Result<(Term, String)> {
        let term = parse(text)?;
        let sort = check(&term, &self.signatures, &mut BTreeMap::new(), work, 16384)?;
        Ok((term, TermLanguage::sort_to_name(&sort)))
    }

    pub(super) fn ground_terms(
        &self,
        roots: &[Term],
        limit: usize,
    ) -> anyhow::Result<Vec<CatalogueTerm>> {
        let mut terms = BTreeMap::new();
        let mut work = 0;
        for term in roots {
            check(term, &self.signatures, &mut terms, &mut work, limit)?;
        }
        Ok(terms
            .into_iter()
            .map(|(expression, (term, sort))| CatalogueTerm {
                id: String::new(),
                expression,
                sort: TermLanguage::sort_to_name(&sort),
                term,
            })
            .collect())
    }
}

fn check(
    term: &Term,
    sigs: &Signatures,
    terms: &mut BTreeMap<String, (Term, Sort)>,
    work: &mut usize,
    limit: usize,
) -> anyhow::Result<Sort> {
    *work += 1;
    anyhow::ensure!(*work <= limit, "term node budget exceeded");
    let bool_sort = smt2parser::vmt::array_abstractor::string_to_sort("Bool");
    let int_sort = smt2parser::vmt::array_abstractor::string_to_sort("Int");
    let real_sort = smt2parser::vmt::array_abstractor::string_to_sort("Real");
    let sort = match term {
        Term::QualIdentifier(id) => {
            let name = id.get_name();
            if name == "true" || name == "false" {
                bool_sort
            } else if let Some((args, sort)) = sigs.get(&name) {
                anyhow::ensure!(args.is_empty(), "function {name} needs arguments");
                sort.clone()
            } else if matches!(
                id,
                smt2parser::concrete::QualIdentifier::Simple {
                    identifier: Identifier::Indexed { .. }
                }
            ) {
                crate::theories::quantifiers::term_sort(term, sigs, &HashMap::new())?
            } else {
                anyhow::bail!("undeclared ground symbol {name}");
            }
        }
        Term::Constant(Constant::String(_) | Constant::Decimal(_)) => {
            anyhow::bail!("string and decimal literals are unsupported by this backend")
        }
        Term::Constant(_) => crate::theories::quantifiers::term_sort(term, sigs, &HashMap::new())?,
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let name = qual_identifier.get_name();
            let sorts = arguments
                .iter()
                .map(|t| check(t, sigs, terms, work, limit))
                .collect::<anyhow::Result<Vec<_>>>()?;
            if let Some((params, result)) = sigs.get(&name) {
                anyhow::ensure!(
                    &sorts == params,
                    "wrong argument sorts or arity for {name}: expected {params:?}, got {sorts:?}"
                );
                result.clone()
            } else {
                let same = sorts.windows(2).all(|s| s[0] == s[1]);
                let bools = sorts.iter().all(|s| *s == bool_sort);
                let numeric = sorts.iter().all(|s| *s == int_sort || *s == real_sort);
                match name.as_str() {
                    "and" | "or" => {
                        anyhow::ensure!(bools, "Boolean arguments required");
                        bool_sort
                    }
                    "not" => {
                        anyhow::ensure!(sorts.len() == 1 && bools, "not needs one Boolean");
                        bool_sort
                    }
                    "=>" => {
                        anyhow::ensure!(sorts.len() == 2 && bools, "Boolean arguments required");
                        bool_sort
                    }
                    "=" => {
                        anyhow::ensure!(
                            sorts.len() == 2 && same,
                            "equality needs same-sort arguments"
                        );
                        bool_sort
                    }
                    "<" | "<=" | ">" | ">=" => {
                        anyhow::ensure!(
                            sorts.len() == 2 && same && numeric,
                            "comparison needs numeric arguments of one sort"
                        );
                        bool_sort
                    }
                    "+" | "*" | "-" => {
                        anyhow::ensure!(
                            !sorts.is_empty() && same && numeric,
                            "arithmetic needs numeric arguments of one sort"
                        );
                        sorts[0].clone()
                    }
                    "div" | "mod" => {
                        anyhow::ensure!(
                            sorts.len() == 2 && sorts.iter().all(|s| *s == int_sort),
                            "integer operands required"
                        );
                        int_sort
                    }
                    "ite" => {
                        anyhow::ensure!(
                            sorts.len() == 3 && sorts[0] == bool_sort && sorts[1] == sorts[2],
                            "ill-typed ite"
                        );
                        sorts[1].clone()
                    }
                    "/" => {
                        anyhow::ensure!(
                            sorts.len() == 2 && same && numeric,
                            "division needs numeric arguments of one sort"
                        );
                        crate::theories::quantifiers::term_sort(term, sigs, &HashMap::new())?
                    }
                    "bvnot" | "bvneg" => {
                        anyhow::ensure!(
                            sorts.len() == 1
                                && TermLanguage::sort_to_name(&sorts[0]).starts_with("BitVec"),
                            "one bitvector required"
                        );
                        sorts[0].clone()
                    }
                    "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor" | "bvshl"
                    | "bvlshr" | "bvashr" | "bvudiv" | "bvsdiv" | "bvurem" | "bvsrem"
                    | "bvsmod" => {
                        anyhow::ensure!(
                            sorts.len() == 2
                                && same
                                && TermLanguage::sort_to_name(&sorts[0]).starts_with("BitVec"),
                            "two same-width bitvectors required"
                        );
                        sorts[0].clone()
                    }
                    "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt"
                    | "bvsge" => {
                        anyhow::ensure!(
                            sorts.len() == 2
                                && same
                                && TermLanguage::sort_to_name(&sorts[0]).starts_with("BitVec"),
                            "two same-width bitvectors required"
                        );
                        bool_sort
                    }
                    "extract" | "zero_extend" | "sign_extend" | "concat" => {
                        crate::theories::quantifiers::term_sort(term, sigs, &HashMap::new())?
                    }
                    _ => anyhow::bail!("unsupported or undeclared function {name}"),
                }
            }
        }
        _ => anyhow::bail!("term must be ground and quantifier-free without let/attributes"),
    };
    let identifier = match term {
        Term::QualIdentifier(id) => Some(id),
        Term::Application {
            qual_identifier, ..
        } => Some(qual_identifier),
        _ => None,
    };
    if let Some(smt2parser::concrete::QualIdentifier::Sorted {
        sort: annotation, ..
    }) = identifier
    {
        anyhow::ensure!(*annotation == sort, "incorrect explicit sort annotation");
    }
    terms.insert(term.to_string(), (term.clone(), sort.clone()));
    Ok(sort)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn accepts(text: &str) -> bool {
        let Ok(term) = parse(text) else {
            return false;
        };
        let int = smt2parser::vmt::array_abstractor::string_to_sort("Int");
        let bool_sort = smt2parser::vmt::array_abstractor::string_to_sort("Bool");
        let signatures = HashMap::from([
            ("f".into(), (vec![int.clone()], int.clone())),
            ("x@0".into(), (vec![], int)),
            ("flag".into(), (vec![], bool_sort)),
        ]);
        check(&term, &signatures, &mut BTreeMap::new(), &mut 0, 256).is_ok()
    }
    #[test]
    fn admission_checks_all_arguments_and_scope() {
        for good in [
            "(+ 1 2)",
            "(f x@0)",
            "(f (f 17))",
            "(ite flag 1 2)",
            "(bvadd #x01 #x02)",
        ] {
            assert!(accepts(good), "{good}");
        }
        for bad in [
            "(f true)",
            "(f 1 2)",
            "f",
            "x@999",
            "Int!val!0",
            "(not 1)",
            "(as x@0 Bool)",
            "1.25",
            "(= 1 true)",
            "(= 0 0 1)",
            "(=> true true false)",
            "(< 1 2 3)",
            "(xor true false)",
            "(distinct 0 1)",
            "(bvnand #x01 #x02)",
            "(forall ((x Int)) (= x 1))",
            "1) (assert false) (assert 1",
            "(bvadd #x01 #x0002)",
        ] {
            assert!(!accepts(bad), "{bad}");
        }
    }
}
