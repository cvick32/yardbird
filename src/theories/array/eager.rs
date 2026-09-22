//! Source-syntax array instances. No solver evaluation or model equalities.
//! Native and abstract sessions share candidate enumeration and cost vocabulary.
use std::collections::{BTreeMap, BTreeSet, HashMap};

use smt2parser::concrete::{Command, Constant, QualIdentifier, Sort, Term};
use smt2parser::vmt::{array_abstractor::string_to_sort, split_framed_symbol, ReadsAndWrites};

use super::eager_source::SourceVocabulary;
use crate::policy::{
    eager::{order, EagerInstantiation},
    term_selection::{context::TermCostContext, TermCostFactory},
};
use crate::terms::language::{translate_term_with_array_types, TermExpr, TermLanguage};
use crate::theories::quantifiers::{abstract_sort, app};

pub(crate) struct Seed {
    pub term: Term,
    pub normalized: TermExpr,
    pub rule: String,
    pub bindings: Vec<(String, Term)>,
    pub cost: u32,
    pub family: String,
}

struct Vocabulary {
    signatures: HashMap<String, Sort>,
    types: Vec<(String, String)>,
}

impl Vocabulary {
    fn new(source: &SourceVocabulary) -> Self {
        let mut signatures = HashMap::new();
        for declaration in source.declarations.iter().cloned() {
            let (name, sort) = match declaration {
                Command::DeclareFun { symbol, sort, .. }
                | Command::DeclareConst { symbol, sort } => (symbol.0, sort),
                Command::DefineFun { sig, .. } => (sig.name.0, sig.result),
                _ => continue,
            };
            signatures.insert(name, sort);
        }
        Self {
            signatures,
            types: source.array_types.clone(),
        }
    }

    // Conservative inference over well-typed source syntax. In particular, do
    // not guess the result width of indexed bitvector operators from operand 0.
    fn sort(&self, term: &Term) -> Option<Sort> {
        match term {
            Term::QualIdentifier(id) => {
                let name = id.get_name();
                if name == "true" || name == "false" {
                    return Some(string_to_sort("Bool"));
                }
                let base = split_framed_symbol(&name)
                    .map(|(base, _)| base)
                    .unwrap_or(name.clone());
                self.signatures
                    .get(&name)
                    .or_else(|| self.signatures.get(&base))
                    .cloned()
            }
            Term::Constant(Constant::Numeral(_)) => Some(string_to_sort("Int")),
            Term::Constant(Constant::Decimal(_)) => Some(string_to_sort("Real")),
            Term::Constant(Constant::Binary(bits)) => {
                Some(string_to_sort(&format!("BitVec{}", bits.len())))
            }
            Term::Constant(Constant::Hexadecimal(digits)) => {
                Some(string_to_sort(&format!("BitVec{}", digits.len() * 4)))
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let name = qual_identifier.get_name();
                if let Some(sort) = self.signatures.get(&name) {
                    return Some(sort.clone());
                }
                if let Some((op, index, value)) = self.abstract_op(&name) {
                    return Some(if op == "Read" {
                        string_to_sort(value)
                    } else {
                        string_to_sort(&format!("Array_{index}_{value}"))
                    });
                }
                match (name.as_str(), arguments.as_slice()) {
                    ("select", [array, _]) => self.array_sorts(array).map(|(_, v)| v),
                    ("store", [array, _, _]) => self.sort(array),
                    ("const", [_]) => match qual_identifier {
                        QualIdentifier::Sorted { sort, .. } => Some(sort.clone()),
                        _ => None,
                    },
                    ("ite", [_, yes, _]) => self.sort(yes),
                    ("+" | "-" | "*" | "div" | "mod" | "abs", [first, ..]) => {
                        let sort = self.sort(first)?;
                        arguments
                            .iter()
                            .all(|arg| self.sort(arg).as_ref() == Some(&sort))
                            .then_some(sort)
                    }
                    ("to_real" | "/", _) => Some(string_to_sort("Real")),
                    ("to_int", [_]) => Some(string_to_sort("Int")),
                    (
                        "and" | "or" | "not" | "=>" | "=" | "distinct" | "<" | "<=" | ">" | ">=",
                        _,
                    ) => Some(string_to_sort("Bool")),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn abstract_op<'a>(&'a self, name: &str) -> Option<(&'static str, &'a str, &'a str)> {
        for (index, value) in &self.types {
            for op in ["Read", "Write", "ConstArr"] {
                if name == format!("{op}_{index}_{value}") {
                    return Some((op, index, value));
                }
            }
        }
        None
    }

    fn array_sorts(&self, term: &Term) -> Option<(Sort, Sort)> {
        match self.sort(term)? {
            Sort::Parameterized {
                identifier,
                parameters,
            } if identifier.to_string() == "Array" && parameters.len() == 2 => {
                Some((parameters[0].clone(), parameters[1].clone()))
            }
            sort => self
                .types
                .iter()
                .find(|(i, v)| sort.to_string() == format!("Array_{i}_{v}"))
                .map(|(i, v)| (string_to_sort(i), string_to_sort(v))),
        }
    }

    fn normalize(&self, term: &Term) -> Option<Term> {
        match term {
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let name = qual_identifier.get_name();
                let op_and_sorts = match (name.as_str(), arguments.as_slice()) {
                    ("select", [array, _]) => Some(("Read", self.array_sorts(array)?)),
                    ("store", [array, _, _]) => Some(("Write", self.array_sorts(array)?)),
                    ("const", [_]) => Some(("ConstArr", self.array_sorts(term)?)),
                    _ => None,
                };
                let identifier = if let Some((op, (i, v))) = op_and_sorts {
                    QualIdentifier::simple(format!("{op}_{}_{}", sort_key(&i), sort_key(&v)))
                } else {
                    qual_identifier.clone()
                };
                Some(Term::Application {
                    qual_identifier: identifier,
                    arguments: arguments
                        .iter()
                        .map(|a| self.normalize(a))
                        .collect::<Option<Vec<_>>>()?,
                })
            }
            Term::QualIdentifier(_) | Term::Constant(_) => Some(term.clone()),
            // No traversal into binders: their bound symbols are not ground seeds.
            _ => None,
        }
    }

    fn expression(&self, term: &Term) -> Option<TermExpr> {
        translate_term_with_array_types(self.normalize(term)?, &self.types)
    }
}

fn sort_key(sort: &Sort) -> String {
    TermLanguage::sort_to_name(&abstract_sort(sort))
}

fn collect(term: &Term, out: &mut BTreeMap<String, Term>) {
    match term {
        Term::Application { arguments, .. } => {
            for arg in arguments {
                collect(arg, out);
            }
            out.insert(term.to_string(), term.clone());
        }
        Term::QualIdentifier(_) | Term::Constant(_) => {
            out.insert(term.to_string(), term.clone());
        }
        _ => {}
    }
}

/// Dependency families deliberately ignore frame suffixes and arithmetic shape.
/// They only influence tie-breaking; they never imply logical equivalence.
fn family(term: &Term) -> String {
    fn visit(term: &Term, symbols: &mut BTreeSet<String>) {
        match term {
            Term::QualIdentifier(id) => {
                let name = id.get_name();
                symbols.insert(
                    split_framed_symbol(&name)
                        .map(|(base, _)| base)
                        .unwrap_or(name),
                );
            }
            Term::Application { arguments, .. } => {
                for arg in arguments {
                    visit(arg, symbols);
                }
            }
            _ => {}
        }
    }
    let mut symbols = BTreeSet::new();
    visit(term, &mut symbols);
    format!("{symbols:?}")
}

struct Site {
    term: Term,
    index_sort: String,
    value_sort: String,
    native: bool,
    // Write: array/index/value. Constant array: value.
    arguments: Vec<Term>,
    indices: Vec<Term>,
}

struct SiteInstance {
    term: Term,
    rule: String,
    bindings: Vec<(String, Term)>,
    index: Term,
}

impl Site {
    fn read(&self, array: Term, index: Term) -> Term {
        let name = if self.native {
            "select".into()
        } else {
            format!("Read_{}_{}", self.index_sort, self.value_sort)
        };
        app(&name, vec![array, index])
    }

    fn instance(&self, round: usize) -> Option<SiteInstance> {
        let (kind, index, rhs, bindings, guard) = match self.arguments.as_slice() {
            [array, written, value] => {
                if round == 0 {
                    (
                        "read-after-write",
                        written.clone(),
                        value.clone(),
                        vec![
                            ("?a".into(), array.clone()),
                            ("?idx".into(), written.clone()),
                            ("?val".into(), value.clone()),
                        ],
                        None,
                    )
                } else {
                    let index = self.indices.get(round - 1)?.clone();
                    let guard = app("not", vec![app("=", vec![index.clone(), written.clone()])]);
                    let rhs = self.read(array.clone(), index.clone());
                    (
                        "write-does-not-overwrite",
                        index.clone(),
                        rhs,
                        vec![
                            ("?a".into(), array.clone()),
                            ("?idx".into(), written.clone()),
                            ("?val".into(), value.clone()),
                            ("?c".into(), index),
                        ],
                        Some(guard),
                    )
                }
            }
            [value] => {
                let index = self.indices.get(round)?.clone();
                (
                    "constant-array",
                    index.clone(),
                    value.clone(),
                    vec![("?a".into(), value.clone()), ("?b".into(), index)],
                    None,
                )
            }
            _ => return None,
        };
        let equality = app("=", vec![self.read(self.term.clone(), index.clone()), rhs]);
        let term = guard.map_or(equality.clone(), |guard| app("=>", vec![guard, equality]));
        Some(SiteInstance {
            term,
            rule: format!("{kind}-{}_{}", self.index_sort, self.value_sort),
            bindings,
            index,
        })
    }
}

pub(crate) fn generate<F: TermCostFactory>(
    source: &SourceVocabulary,
    cost_config: &F::Config,
    config: EagerInstantiation,
    abstract_arrays: bool,
) -> Vec<Seed> {
    if config.max_candidates == 0 || config.max_instances == 0 {
        return vec![];
    }
    let vocabulary = Vocabulary::new(source);
    let mut initial_and_transition = BTreeMap::new();
    let mut property = BTreeMap::new();
    for term in &source.initial_and_transition {
        collect(term, &mut initial_and_transition);
    }
    for term in &source.property {
        collect(term, &mut property);
    }
    let normalize_list = |terms: &BTreeMap<String, Term>| {
        terms
            .values()
            .filter_map(|term| vocabulary.normalize(term).map(|t| t.to_string()))
            .collect::<Vec<_>>()
    };
    let initial_cost_terms = normalize_list(&initial_and_transition);
    let property_cost_terms = normalize_list(&property);
    let mut terms = initial_and_transition;
    terms.extend(property);
    let mut reads_writes = ReadsAndWrites::default();
    for term in terms.values().filter_map(|t| vocabulary.normalize(t)) {
        let _ = term.accept_term_visitor(&mut reads_writes);
    }
    let context =
        TermCostContext::source_vocabulary(initial_cost_terms, property_cost_terms, reads_writes);
    let cost = F::from_context(&context, 0, cost_config);
    // Clone for each score: some experimental cost functions keep mutable state.
    let score = |term: &Term| {
        vocabulary
            .expression(term)
            .map(|e| (cost.clone().cost_rec(&e), e))
    };
    let mut pools = BTreeMap::<String, Vec<_>>::new();
    for term in terms.values() {
        if let (Some(sort), Some((cost, expression))) = (vocabulary.sort(term), score(term)) {
            pools.entry(sort_key(&sort)).or_default().push((
                cost,
                family(term),
                expression.to_string(),
                term.clone(),
            ));
        }
    }
    let pools = pools
        .into_iter()
        .map(|(sort, terms)| {
            (
                sort,
                order(terms, config.max_candidates, config.diversify_ties),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut sites = Vec::new();
    for term in terms.values() {
        let Term::Application {
            qual_identifier,
            arguments,
        } = term
        else {
            continue;
        };
        let name = qual_identifier.get_name();
        let native = name == "store" || name == "const";
        let sorts = if native {
            vocabulary
                .array_sorts(term)
                .map(|(i, v)| (sort_key(&i), sort_key(&v)))
        } else {
            vocabulary
                .abstract_op(&name)
                .filter(|(op, _, _)| *op == "Write" || *op == "ConstArr")
                .map(|(_, i, v)| (i.to_owned(), v.to_owned()))
        };
        let Some((index_sort, value_sort)) = sorts else {
            continue;
        };
        if arguments.len() != 1 && arguments.len() != 3 {
            continue;
        }
        let Some((cost, expr)) = score(term) else {
            continue;
        };
        let mut indices = pools.get(&index_sort).cloned().unwrap_or_default();
        if arguments.len() == 3 {
            indices.retain(|i| i != &arguments[1]);
        }
        sites.push((
            cost,
            family(term),
            expr.to_string(),
            Site {
                term: term.clone(),
                index_sort,
                value_sort,
                native,
                arguments: arguments.clone(),
                indices,
            },
        ));
    }
    let sites = order(sites, config.max_candidates, config.diversify_ties);
    let mut seeds = Vec::new();
    // Breadth across sites before taking another index from the same site.
    for round in 0..=config.max_candidates {
        let mut any = false;
        for site in &sites {
            let Some(SiteInstance {
                term,
                rule,
                bindings,
                index,
            }) = site.instance(round)
            else {
                continue;
            };
            any = true;
            if let Some((cost, normalized)) = score(&term) {
                let family = format!("{rule}:{}:{}", family(&site.term), family(&index));
                // Selection and scoring always use the original source. Only
                // the asserted formula and its bindings depend on the solver encoding.
                let (term, bindings) = if abstract_arrays {
                    (
                        vocabulary.normalize(&term).unwrap(),
                        bindings
                            .into_iter()
                            .map(|(name, value)| (name, vocabulary.normalize(&value).unwrap()))
                            .collect(),
                    )
                } else {
                    (term, bindings)
                };
                seeds.push(Seed {
                    term,
                    normalized,
                    rule,
                    bindings,
                    cost,
                    family,
                });
                if seeds.len() == config.max_candidates {
                    return seeds;
                }
            }
        }
        if !any {
            break;
        }
    }
    seeds
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn families_ignore_offsets_and_frames_but_preserve_dependencies() {
        assert_eq!(
            family(&"(+ i@0 1)".parse().unwrap()),
            family(&"(+ i@3 2)".parse().unwrap())
        );
        assert_ne!(
            family(&"i@0".parse().unwrap()),
            family(&"j@0".parse().unwrap())
        );
    }
}
