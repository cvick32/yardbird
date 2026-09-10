//! Closure conversion for quantified formulas and SMT array lambdas.
//!
//! A helper denotes the value of each binder expression as a function of its
//! free variables. Universal instances constrain one direction; a Skolem
//! witness constrains the other. Keeping both directions makes this valid in
//! arbitrary Boolean positions, including negated and alternating quantifiers.
use std::collections::{BTreeMap, HashMap, HashSet};

use smt2parser::{
    concrete::{Command, Constant, Identifier, QualIdentifier, Sort, Symbol, Term},
    let_extract::LetExtract,
    vmt::{array_abstractor::string_to_sort, split_framed_symbol, VMTModel},
};

use crate::theories::array::array_axioms::ArrayLanguage;
use crate::{
    instantiation_provenance::InstantiationProvenance,
    quantified_rule::QuantifiedRule,
    theories::array::{
        array_axioms::translate_term_with_array_types,
        instantiation_candidate::{CandidateGroup, InstantiationCandidate, InstantiationGrounding},
    },
};

pub(crate) fn app(name: &str, arguments: Vec<Term>) -> Term {
    if arguments.is_empty() {
        Term::QualIdentifier(QualIdentifier::simple(name))
    } else {
        Term::Application {
            qual_identifier: QualIdentifier::simple(name),
            arguments,
        }
    }
}

pub(crate) fn substitute(term: Term, bindings: Vec<(Symbol, Term)>) -> Term {
    LetExtract::substitute(Term::Let {
        var_bindings: bindings,
        term: Box::new(term),
    })
}

fn sort_name(sort: &Sort) -> String {
    match sort {
        Sort::Parameterized {
            identifier,
            parameters,
        } => format!(
            "{}_{}",
            identifier,
            parameters
                .iter()
                .map(sort_name)
                .collect::<Vec<_>>()
                .join("_")
        ),
        _ => ArrayLanguage::sort_to_name(sort),
    }
}

fn abstract_sort(sort: &Sort) -> Sort {
    match sort {
        Sort::Parameterized { identifier, .. } if identifier.to_string() == "Array" => {
            string_to_sort(&sort_name(sort))
        }
        _ => sort.clone(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BinderKind {
    Forall,
    Exists,
    Lambda,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum SearchPhase {
    Witnesses,
    Conflicts,
    Expand,
}

#[derive(Clone, Debug)]
pub(crate) struct BinderRule {
    pub name: String,
    pub kind: BinderKind,
    pub captures: Vec<(Symbol, Sort)>,
    pub variables: Vec<(Symbol, Sort)>,
    pub body: Term,
    pub witnesses: Vec<String>,
    pub result_sort: Sort,
}

impl BinderRule {
    pub fn instantiate(&self, arguments: &[Term], values: &[Term]) -> Term {
        let bindings = self
            .captures
            .iter()
            .map(|(s, _)| s.clone())
            .zip(arguments.iter().cloned())
            .chain(
                self.variables
                    .iter()
                    .map(|(s, _)| s.clone())
                    .zip(values.iter().cloned()),
            )
            .collect();
        let body = substitute(self.body.clone(), bindings);
        let proxy = app(&self.name, arguments.to_vec());
        match self.kind {
            BinderKind::Forall => app("=>", vec![proxy, body]),
            BinderKind::Exists => app("=>", vec![body, proxy]),
            BinderKind::Lambda => {
                let mut read = proxy;
                let mut sort = self.result_sort.clone();
                // The native result sort is retained for recovering nested read types.
                for (value, (_, index)) in values.iter().zip(&self.variables) {
                    let Sort::Parameterized { parameters, .. } = sort else {
                        unreachable!()
                    };
                    sort = parameters[1].clone();
                    read = app(
                        &format!("Read_{}_{}", sort_name(index), sort_name(&sort)),
                        vec![read, value.clone()],
                    );
                }
                app("=", vec![read, body])
            }
        }
    }

    pub fn witness_instance(&self, arguments: &[Term]) -> Option<Term> {
        if self.kind == BinderKind::Lambda {
            return None;
        }
        let values = self
            .witnesses
            .iter()
            .map(|name| app(name, arguments.to_vec()))
            .collect::<Vec<_>>();
        let bindings = self
            .captures
            .iter()
            .map(|(s, _)| s.clone())
            .zip(arguments.iter().cloned())
            .chain(self.variables.iter().map(|(s, _)| s.clone()).zip(values))
            .collect();
        let body = substitute(self.body.clone(), bindings);
        let proxy = app(&self.name, arguments.to_vec());
        Some(match self.kind {
            BinderKind::Forall => app("=>", vec![app("not", vec![proxy]), app("not", vec![body])]),
            BinderKind::Exists => app("=>", vec![proxy, body]),
            BinderKind::Lambda => unreachable!(),
        })
    }
}

#[derive(Default)]
pub(crate) struct QuantifierPlan {
    pub rules: Vec<BinderRule>,
    pub signatures: HashMap<String, (Vec<Sort>, Sort)>,
    pub seeds: Vec<(Sort, Term)>,
}

impl QuantifierPlan {
    pub fn sort_of(&self, term: &Term) -> Option<Sort> {
        term_sort(term, &self.signatures, &HashMap::new()).ok()
    }

    /// Search ground tuples by sort and model value. Bounds limit one search
    /// pass, never establish satisfiability or completeness of a finite domain.
    pub fn candidates(
        &self,
        smt: &dyn crate::problem_context::ProblemContext,
        phase: SearchPhase,
    ) -> anyhow::Result<Vec<InstantiationCandidate>> {
        if self.rules.is_empty() {
            return Ok(vec![]);
        }
        use crate::instantiation_strategy::assertion_tracker::canonical_instantiation_key;
        let known = smt
            .get_instantiations()
            .iter()
            .map(canonical_instantiation_key)
            .collect::<HashSet<_>>();
        let mut terms = smt
            .get_all_subterms()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        terms.extend(self.seeds.iter().map(|(_, term)| term.clone()));
        terms.extend([app("true", vec![]), app("false", vec![]), "0".parse()?]);
        terms.sort_by_cached_key(|term| {
            let text = term.to_string();
            (text.len(), text)
        });
        terms.dedup();
        let mut pools = HashMap::<Sort, Vec<Term>>::new();
        let mut values = HashSet::new();
        let needed_sorts = self
            .rules
            .iter()
            .flat_map(|rule| rule.variables.iter().map(|(_, sort)| sort))
            .collect::<HashSet<_>>();
        for term in &terms {
            if let Some(sort) = self.sort_of(term) {
                if !needed_sorts.contains(&sort) {
                    continue;
                }
                let value = smt.eval_to_string(term)?;
                if values.insert((sort.clone(), value)) {
                    pools.entry(sort).or_default().push(term.clone());
                }
            }
        }
        let rules = self
            .rules
            .iter()
            .map(|rule| (rule.name.as_str(), rule))
            .collect::<HashMap<_, _>>();
        let mut result = Vec::new();
        let mut seen = HashSet::new();
        for term in &terms {
            let Term::Application {
                qual_identifier,
                arguments,
            } = term
            else {
                continue;
            };
            let name = qual_identifier.get_name();
            let Some(rule) = rules.get(name.as_str()) else {
                continue;
            };
            let mut accept = |instance: Term, tuple: &[Term]| -> anyhow::Result<bool> {
                let Some(normalized) = smt.make_unquantified_instance(instance.clone()) else {
                    return Ok(false);
                };
                let key = canonical_instantiation_key(normalized.get_term());
                if known.contains(&key) || !seen.insert(key) {
                    return Ok(false);
                }
                if phase == SearchPhase::Expand || smt.eval_to_string(&instance)?.trim() == "false"
                {
                    let expression =
                        translate_term_with_array_types(instance, &smt.get_array_types())
                            .ok_or_else(|| {
                                anyhow::anyhow!(
                                    "could not translate binder instance for {}",
                                    rule.name
                                )
                            })?;
                    let substitution = rule
                        .captures
                        .iter()
                        .map(|(s, _)| s.0.clone())
                        .zip(arguments.iter().cloned())
                        .chain(
                            rule.variables
                                .iter()
                                .map(|(s, _)| s.0.clone())
                                .zip(tuple.iter().cloned()),
                        )
                        .collect();
                    let provenance = InstantiationProvenance::new(
                        format!(
                            "{}:{}",
                            rule.name,
                            crate::training::canonical_term_hash(&expression)
                        ),
                        substitution,
                    );
                    result.push(InstantiationCandidate {
                        rule: QuantifiedRule::input_binder(&rule.name),
                        cost: expression.as_ref().len() as u32,
                        expression,
                        grounding: InstantiationGrounding::Derived,
                        provenance,
                        selected: true,
                        decisions: vec![],
                        selection_history: vec![],
                        abstract_instantiation: None,
                        conflict: None,
                        group: CandidateGroup::Rule,
                        model_violation_verified: phase != SearchPhase::Expand,
                    });
                }
                Ok(result.len() >= 128)
            };
            let proxy_value = if rule.kind == BinderKind::Lambda {
                String::new()
            } else {
                smt.eval_to_string(term)?
            };
            let witness_active = (rule.kind == BinderKind::Forall && proxy_value.trim() == "false")
                || (rule.kind == BinderKind::Exists && proxy_value.trim() == "true");
            if witness_active {
                if let Some(instance) = rule.witness_instance(arguments) {
                    let tuple = rule
                        .witnesses
                        .iter()
                        .map(|name| app(name, arguments.clone()))
                        .collect::<Vec<_>>();
                    accept(instance, &tuple)?;
                }
            } else if phase != SearchPhase::Witnesses {
                let choices = rule
                    .variables
                    .iter()
                    .map(|(_, sort)| pools.get(sort).cloned().unwrap_or_default())
                    .collect::<Vec<_>>();
                let mut indices = vec![0; choices.len()];
                if choices.iter().any(Vec::is_empty) {
                    continue;
                }
                for _ in 0..4096 {
                    let tuple = choices
                        .iter()
                        .zip(&indices)
                        .map(|(pool, index)| pool[*index].clone())
                        .collect::<Vec<_>>();
                    if accept(rule.instantiate(arguments, &tuple), &tuple)? {
                        break;
                    }
                    let mut position = indices.len();
                    while position > 0 {
                        position -= 1;
                        indices[position] += 1;
                        if indices[position] < choices[position].len() {
                            break;
                        }
                        indices[position] = 0;
                    }
                    if position == 0 && (indices.is_empty() || indices[0] == 0) {
                        break;
                    }
                }
            }
            if result.len() >= 128 {
                break;
            }
        }
        result.truncate(128);
        Ok(result)
    }
}

struct Lowerer {
    signatures: HashMap<String, (Vec<Sort>, Sort)>,
    reserved: HashSet<String>,
    next_id: usize,
    declarations: Vec<Command>,
    rules: Vec<BinderRule>,
}

fn term_sort(
    term: &Term,
    signatures: &HashMap<String, (Vec<Sort>, Sort)>,
    scope: &HashMap<String, Sort>,
) -> anyhow::Result<Sort> {
    match term {
        Term::QualIdentifier(id) => {
            let name = id.get_name();
            if name == "true" || name == "false" {
                return Ok(string_to_sort("Bool"));
            }
            if let Some(sort) = scope.get(&name) {
                return Ok(sort.clone());
            }
            let base = split_framed_symbol(&name)
                .map(|(name, _)| name)
                .unwrap_or(name.clone());
            signatures
                .get(&base)
                .or_else(|| signatures.get(base.trim_matches('|')))
                .map(|(_, sort)| sort.clone())
                .ok_or_else(|| anyhow::anyhow!("unknown sort for {name}"))
        }
        Term::Constant(Constant::Numeral(_)) => Ok(string_to_sort("Int")),
        Term::Constant(Constant::Decimal(_)) => Ok(string_to_sort("Real")),
        Term::Constant(Constant::Binary(bits)) => {
            Ok(string_to_sort(&format!("BitVec{}", bits.len())))
        }
        Term::Constant(Constant::Hexadecimal(digits)) => {
            Ok(string_to_sort(&format!("BitVec{}", digits.len() * 4)))
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let name = qual_identifier.get_name();
            if let Some((_, sort)) = signatures.get(&name) {
                return Ok(sort.clone());
            }
            match name.as_str() {
                "and" | "or" | "not" | "=>" | "=" | "distinct" | "<" | "<=" | ">" | ">="
                | "xor" => Ok(string_to_sort("Bool")),
                "ite" => term_sort(&arguments[1], signatures, scope),
                "select" => match term_sort(&arguments[0], signatures, scope)? {
                    Sort::Parameterized { parameters, .. } => Ok(parameters[1].clone()),
                    sort => anyhow::bail!("select requires an array, got {sort}"),
                },
                "const" => match qual_identifier {
                    QualIdentifier::Sorted { sort, .. } => Ok(sort.clone()),
                    _ => anyhow::bail!("array constant needs a sort"),
                },
                "to_real" => Ok(string_to_sort("Real")),
                "to_int" => Ok(string_to_sort("Int")),
                _ if name.starts_with("Read_") => {
                    // Read signatures are registered when native selects are lowered.
                    anyhow::bail!("unregistered abstract array function {name}")
                }
                _ if !arguments.is_empty() => term_sort(&arguments[0], signatures, scope),
                _ => anyhow::bail!("cannot determine result sort of {term}"),
            }
        }
        Term::Forall { .. } | Term::Exists { .. } => Ok(string_to_sort("Bool")),
        Term::Lambda { vars, term } => {
            let mut inner = scope.clone();
            inner.extend(vars.iter().map(|(s, t)| (s.0.clone(), t.clone())));
            let result = term_sort(term, signatures, &inner)?;
            Ok(vars
                .iter()
                .rev()
                .fold(result, |result, (_, index)| Sort::Parameterized {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Array".into()),
                    },
                    parameters: vec![index.clone(), result],
                }))
        }
        Term::Attributes { term, .. } => term_sort(term, signatures, scope),
        Term::Let { .. } => term_sort(&LetExtract::substitute(term.clone()), signatures, scope),
        _ => anyhow::bail!("unsupported binder body {term}"),
    }
}

impl Lowerer {
    fn fresh(&mut self, kind: &str) -> String {
        loop {
            let name = format!("__yardbird_{kind}_{}", self.next_id);
            self.next_id += 1;
            if self.reserved.insert(name.clone()) {
                return name;
            }
        }
    }

    fn declare(&mut self, name: String, parameters: Vec<Sort>, sort: Sort) {
        self.signatures
            .insert(name.clone(), (parameters.clone(), sort.clone()));
        self.declarations.push(Command::DeclareFun {
            symbol: Symbol(name),
            parameters,
            sort,
        });
    }

    fn array_function(&mut self, name: String, parameters: Vec<Sort>, sort: Sort) {
        if !self.signatures.contains_key(&name) {
            self.declare(name, parameters, sort);
        }
    }

    fn lower(&mut self, term: Term, scope: &HashMap<String, Sort>) -> anyhow::Result<Term> {
        match term {
            Term::Forall { vars, term } => self.binder(BinderKind::Forall, vars, *term, scope),
            Term::Exists { vars, term } => self.binder(BinderKind::Exists, vars, *term, scope),
            Term::Lambda { vars, term } => self.binder(BinderKind::Lambda, vars, *term, scope),
            Term::Attributes { term, attributes } => Ok(Term::Attributes {
                term: Box::new(self.lower(*term, scope)?),
                attributes,
            }),
            Term::Let { .. } => self.lower(LetExtract::substitute(term), scope),
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let name = qual_identifier.get_name();
                let array_sort = if name == "select" || name == "store" {
                    Some(term_sort(&arguments[0], &self.signatures, scope)?)
                } else {
                    None
                };
                let arguments = arguments
                    .into_iter()
                    .map(|arg| self.lower(arg, scope))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                if name == "distinct" {
                    let mut pairs = Vec::new();
                    for left in 0..arguments.len() {
                        for right in left + 1..arguments.len() {
                            pairs.push(app(
                                "not",
                                vec![app(
                                    "=",
                                    vec![arguments[left].clone(), arguments[right].clone()],
                                )],
                            ));
                        }
                    }
                    return Ok(if pairs.is_empty() {
                        app("true", vec![])
                    } else {
                        app("and", pairs)
                    });
                }
                if name == "const" {
                    if let QualIdentifier::Sorted {
                        sort: Sort::Parameterized { parameters, .. },
                        ..
                    } = &qual_identifier
                    {
                        let function = format!(
                            "ConstArr_{}_{}",
                            sort_name(&parameters[0]),
                            sort_name(&parameters[1])
                        );
                        let result = Sort::Parameterized {
                            identifier: Identifier::Simple {
                                symbol: Symbol("Array".into()),
                            },
                            parameters: parameters.clone(),
                        };
                        self.array_function(function.clone(), vec![parameters[1].clone()], result);
                        return Ok(app(&function, arguments));
                    }
                }
                if let Some(Sort::Parameterized { parameters, .. }) = array_sort {
                    let index = &parameters[0];
                    let value = &parameters[1];
                    let function = format!(
                        "{}_{}_{}",
                        if name == "select" { "Read" } else { "Write" },
                        sort_name(index),
                        sort_name(value)
                    );
                    // These signatures are also needed while lowering enclosing lambdas.
                    let array = Sort::Parameterized {
                        identifier: Identifier::Simple {
                            symbol: Symbol("Array".into()),
                        },
                        parameters: parameters.clone(),
                    };
                    let result = if name == "select" {
                        value.clone()
                    } else {
                        array.clone()
                    };
                    let mut sorts = vec![array, index.clone()];
                    if name == "store" {
                        sorts.push(value.clone());
                    }
                    self.array_function(function.clone(), sorts, result);
                    Ok(app(&function, arguments))
                } else {
                    Ok(Term::Application {
                        qual_identifier,
                        arguments,
                    })
                }
            }
            Term::Match { .. } => {
                anyhow::bail!("match expressions are not supported by quantifier abstraction")
            }
            other => Ok(other),
        }
    }

    fn binder(
        &mut self,
        kind: BinderKind,
        vars: Vec<(Symbol, Sort)>,
        body: Term,
        scope: &HashMap<String, Sort>,
    ) -> anyhow::Result<Term> {
        let mut inner = scope.clone();
        let mut renaming = Vec::new();
        let variables = vars
            .into_iter()
            .map(|(symbol, sort)| {
                let fresh = self.fresh("bound");
                renaming.push((symbol, app(&fresh, vec![])));
                inner.insert(fresh.clone(), sort.clone());
                (Symbol(fresh), sort)
            })
            .collect::<Vec<_>>();
        let body = self.lower(substitute(body, renaming), &inner)?;
        let result_sort = if kind == BinderKind::Lambda {
            let result = term_sort(&body, &self.signatures, &inner)?;
            variables
                .iter()
                .rev()
                .fold(result, |result, (_, index)| Sort::Parameterized {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Array".into()),
                    },
                    parameters: vec![index.clone(), result],
                })
        } else {
            string_to_sort("Bool")
        };
        if kind == BinderKind::Lambda {
            let mut depends_on_binder = false;
            collect_symbols(&body, &mut |name| {
                depends_on_binder |= variables.iter().any(|(symbol, _)| symbol.0 == name);
            });
            if !depends_on_binder {
                let mut value_sort = term_sort(&body, &self.signatures, &inner)?;
                let mut constant = body;
                for (_, index) in variables.iter().rev() {
                    let function =
                        format!("ConstArr_{}_{}", sort_name(index), sort_name(&value_sort));
                    let element_sort = value_sort;
                    value_sort = Sort::Parameterized {
                        identifier: Identifier::Simple {
                            symbol: Symbol("Array".into()),
                        },
                        parameters: vec![index.clone(), element_sort.clone()],
                    };
                    self.array_function(function.clone(), vec![element_sort], value_sort.clone());
                    constant = app(&function, vec![constant]);
                }
                return Ok(constant);
            }
        }
        let mut free = BTreeMap::new();
        collect_symbols(&body, &mut |name| {
            if variables.iter().any(|(s, _)| s.0 == name) {
                return;
            }
            if let Some(sort) = inner.get(name).or_else(|| {
                self.signatures
                    .get(name)
                    .filter(|(params, _)| params.is_empty())
                    .map(|(_, sort)| sort)
            }) {
                free.insert(name.to_string(), sort.clone());
            }
        });
        let mut captures = free
            .into_iter()
            .map(|(s, t)| (Symbol(s), t))
            .collect::<Vec<_>>();
        let mut arguments = captures
            .iter()
            .map(|(s, _)| app(&s.0, vec![]))
            .collect::<Vec<_>>();
        // Helpers always have an argument, so VMT never classifies a rigid
        // helper as a per-frame input variable.
        if captures.is_empty() {
            captures.push((Symbol(self.fresh("unit")), string_to_sort("Bool")));
            arguments.push(app("true", vec![]));
        }
        let name = self.fresh(if kind == BinderKind::Lambda {
            "lambda"
        } else {
            "quantifier"
        });
        let parameters = captures
            .iter()
            .map(|(_, sort)| sort.clone())
            .collect::<Vec<_>>();
        self.declare(name.clone(), parameters.clone(), result_sort.clone());
        let witnesses = if kind == BinderKind::Lambda {
            vec![]
        } else {
            variables
                .iter()
                .map(|(_, sort)| {
                    let witness = self.fresh("witness");
                    self.declare(witness.clone(), parameters.clone(), sort.clone());
                    witness
                })
                .collect()
        };
        self.rules.push(BinderRule {
            name: name.clone(),
            kind,
            captures,
            variables,
            body,
            witnesses,
            result_sort,
        });
        Ok(app(&name, arguments))
    }
}

fn collect_symbols(term: &Term, visit: &mut impl FnMut(&str)) {
    match term {
        Term::QualIdentifier(id) => visit(&id.get_name()),
        Term::Application { arguments, .. } => {
            for term in arguments {
                collect_symbols(term, visit);
            }
        }
        Term::Attributes { term, .. } => collect_symbols(term, visit),
        _ => {}
    }
}

pub(crate) fn contains_binders(term: &Term) -> bool {
    match term {
        Term::Forall { .. } | Term::Exists { .. } | Term::Lambda { .. } => true,
        Term::Application { arguments, .. } => arguments.iter().any(contains_binders),
        Term::Let { var_bindings, term } => {
            var_bindings.iter().any(|(_, term)| contains_binders(term)) || contains_binders(term)
        }
        Term::Attributes { term, .. } => contains_binders(term),
        Term::Match { term, cases } => {
            contains_binders(term) || cases.iter().any(|(_, term)| contains_binders(term))
        }
        _ => false,
    }
}

/// Rename lexical binders before let expansion or property Herbrandization.
/// In `(let ((a x)) (forall ((x S)) a))`, expanding `a` must not capture
/// the free `x`. Fresh binder names make the existing let substitution safe.
pub(crate) fn scope_binders(model: VMTModel) -> anyhow::Result<VMTModel> {
    fn rewrite(
        term: Term,
        scope: &HashMap<String, String>,
        reserved: &mut HashSet<String>,
        next: &mut usize,
    ) -> Term {
        match term {
            Term::QualIdentifier(id) => scope
                .get(&id.get_name())
                .map(|name| app(name, vec![]))
                .unwrap_or(Term::QualIdentifier(id)),
            Term::Application {
                qual_identifier,
                arguments,
            } => Term::Application {
                qual_identifier,
                arguments: arguments
                    .into_iter()
                    .map(|term| rewrite(term, scope, reserved, next))
                    .collect(),
            },
            Term::Attributes { term, attributes } => Term::Attributes {
                term: Box::new(rewrite(*term, scope, reserved, next)),
                attributes,
            },
            Term::Let { var_bindings, term } => {
                let mut inner = scope.clone();
                for (symbol, _) in &var_bindings {
                    inner.remove(&symbol.0);
                }
                Term::Let {
                    var_bindings: var_bindings
                        .into_iter()
                        .map(|(symbol, term)| (symbol, rewrite(term, scope, reserved, next)))
                        .collect(),
                    term: Box::new(rewrite(*term, &inner, reserved, next)),
                }
            }
            term @ (Term::Forall { .. } | Term::Exists { .. } | Term::Lambda { .. }) => {
                let kind = match &term {
                    Term::Forall { .. } => BinderKind::Forall,
                    Term::Exists { .. } => BinderKind::Exists,
                    _ => BinderKind::Lambda,
                };
                let (vars, term) = match term {
                    Term::Forall { vars, term }
                    | Term::Exists { vars, term }
                    | Term::Lambda { vars, term } => (vars, term),
                    _ => unreachable!(),
                };
                let mut inner = scope.clone();
                let vars = vars
                    .into_iter()
                    .map(|(symbol, sort)| {
                        let name = loop {
                            let name = format!("__yardbird_scoped_binder_{next}");
                            *next += 1;
                            if reserved.insert(name.clone()) {
                                break name;
                            }
                        };
                        inner.insert(symbol.0, name.clone());
                        (Symbol(name), sort)
                    })
                    .collect();
                let term = Box::new(rewrite(*term, &inner, reserved, next));
                match kind {
                    BinderKind::Forall => Term::Forall { vars, term },
                    BinderKind::Exists => Term::Exists { vars, term },
                    BinderKind::Lambda => Term::Lambda { vars, term },
                }
            }
            other => other,
        }
    }
    let commands = model.as_commands();
    let mut reserved = commands
        .iter()
        .flat_map(|command| {
            command
                .to_string()
                .split(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | '|'))
                .map(str::to_string)
                .collect::<Vec<_>>()
        })
        .collect();
    let mut next = 0;
    let commands = commands
        .into_iter()
        .map(|command| match command {
            Command::DefineFun { sig, term } => Command::DefineFun {
                sig,
                term: rewrite(term, &HashMap::new(), &mut reserved, &mut next),
            },
            Command::Assert { term } => Command::Assert {
                term: rewrite(term, &HashMap::new(), &mut reserved, &mut next),
            },
            other => other,
        })
        .collect();
    Ok(VMTModel::checked_from(commands)?)
}

/// Lower every binder before array abstraction, including helper definitions
/// and background assertions. The returned model contains no binder terms.
pub(crate) fn lower_model(model: VMTModel) -> anyhow::Result<(VMTModel, QuantifierPlan)> {
    let commands = model.as_commands();
    if !commands.iter().any(|command| match command {
        Command::DefineFun { term, .. } | Command::Assert { term } => contains_binders(term),
        _ => false,
    }) {
        return Ok((model, QuantifierPlan::default()));
    }
    let mut signatures = HashMap::new();
    for command in &commands {
        match command {
            Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                signatures.insert(symbol.0.clone(), (parameters.clone(), sort.clone()));
            }
            Command::DefineFun { sig, .. } => {
                signatures.insert(
                    sig.name.0.clone(),
                    (
                        sig.parameters
                            .iter()
                            .map(|(_, sort)| sort.clone())
                            .collect(),
                        sig.result.clone(),
                    ),
                );
            }
            _ => {}
        }
    }
    // Reserve binder and local names as well as global declarations.
    let mut reserved = signatures.keys().cloned().collect::<HashSet<_>>();
    for command in &commands {
        for token in command
            .to_string()
            .split(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == '|')
        {
            reserved.insert(token.to_string());
        }
    }
    let mut lowerer = Lowerer {
        signatures,
        reserved,
        next_id: 0,
        declarations: vec![],
        rules: vec![],
    };
    let mut lowered = Vec::new();
    for command in commands {
        lowered.push(match command {
            Command::DefineFun { sig, term } => {
                let scope = sig
                    .parameters
                    .iter()
                    .map(|(s, t)| (s.0.clone(), t.clone()))
                    .collect();
                Command::DefineFun {
                    sig,
                    term: lowerer.lower(term, &scope)?,
                }
            }
            Command::Assert { term } => Command::Assert {
                term: lowerer.lower(term, &HashMap::new())?,
            },
            other => other,
        });
    }
    let mut seeds = Vec::new();
    let sorts = lowerer
        .rules
        .iter()
        .flat_map(|rule| rule.variables.iter().map(|(_, sort)| sort.clone()))
        .collect::<HashSet<_>>();
    let mut sorts = sorts.into_iter().collect::<Vec<_>>();
    sorts.sort_by_key(ToString::to_string);
    for sort in sorts {
        let name = lowerer.fresh("seed");
        lowerer.declare(name.clone(), vec![string_to_sort("Bool")], sort.clone());
        seeds.push((abstract_sort(&sort), app(&name, vec![app("true", vec![])])));
    }
    // Declare closures before any zero-argument helpers that use them.
    let mut declarations = lowerer.declarations;
    declarations.extend(lowered);
    let model = VMTModel::checked_from(declarations)?;
    for rule in &mut lowerer.rules {
        for (_, sort) in rule.captures.iter_mut().chain(&mut rule.variables) {
            *sort = abstract_sort(sort);
        }
    }
    let signatures = lowerer
        .signatures
        .into_iter()
        .map(|(name, (params, result))| {
            (
                name,
                (
                    params.iter().map(abstract_sort).collect(),
                    abstract_sort(&result),
                ),
            )
        })
        .collect();
    Ok((
        model,
        QuantifierPlan {
            rules: lowerer.rules,
            signatures,
            seeds,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Driver, SolverBackend, Strategy, YardbirdOptions};

    fn model(source: &str) -> VMTModel {
        let commands = smt2parser::CommandStream::new(
            std::io::Cursor::new(source.as_bytes()),
            smt2parser::concrete::SyntaxBuilder,
            None,
        )
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
        VMTModel::checked_from(commands).unwrap()
    }

    fn formula_model(init: &str, property: &str) -> VMTModel {
        model(&format!(
            "(declare-fun a () (Array Bool Bool))
            (define-fun init () Bool (! {init} :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! {property} :invar-property 0))"
        ))
    }

    fn check(init: &str, property: &str) -> crate::Result<crate::ProofLoopResult> {
        check_model(formula_model(init, property))
    }

    fn check_model(model: VMTModel) -> crate::Result<crate::ProofLoopResult> {
        let mut options = YardbirdOptions::from_filename("unused.vmt".into());
        options.strategy = Strategy::Abstract;
        let mut driver = Driver::new(
            model,
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        );
        driver.check_strategy(1, options.build_array_strategy())
    }

    #[test]
    fn let_aliases_are_not_captured_by_quantifiers_or_property_witnesses() {
        let source = |init: &str, property: &str| {
            model(&format!(
                "(declare-fun a () (Array Bool Bool))
            (declare-fun x () Bool)
            (define-fun init () Bool (! {init} :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! {property} :invar-property 0))"
            ))
        };
        let alias = "(let ((alias x)) (forall ((x Bool)) alias))";
        assert!(check_model(source("x", alias)).is_ok());
        assert!(matches!(
            check_model(source(&format!("(and x {alias})"), "false")),
            Err(crate::Error::AbstractionExhausted { .. })
        ));
    }

    #[test]
    fn arrays_that_only_occur_in_binder_expressions_are_declared() {
        let result = check_model(model("(define-fun init () Bool (! true :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! (forall ((x Bool)) (select (lambda ((y Bool)) true) x)) :invar-property 0))")).unwrap();
        assert!(!result.counterexample);
    }

    #[test]
    fn arithmetic_hidden_in_a_quantifier_selects_a_sufficient_logic() {
        assert!(check("(forall ((x Int)) (< (* x x) 0))", "false").is_ok());
    }

    #[test]
    fn every_protocol_lowers_to_quantifier_free_commands_and_rules() {
        let root =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/distributed_protocols");
        let mut files = Vec::new();
        for directory in std::fs::read_dir(root).unwrap().flatten() {
            if !directory.path().is_dir() {
                continue;
            }
            for entry in std::fs::read_dir(directory.path()).unwrap().flatten() {
                if entry
                    .path()
                    .extension()
                    .is_some_and(|extension| extension == "vmt")
                {
                    files.push(entry.path());
                }
            }
        }
        assert!(files.len() >= 30, "protocol inventory unexpectedly shrank");
        files.sort();
        for file in files {
            let (lowered, plan) = lower_model(VMTModel::from_path(&file).unwrap())
                .unwrap_or_else(|error| panic!("{}: {error}", file.display()));
            let (abstracted, _) = lowered.abstract_array_theory();
            for command in abstracted.as_commands() {
                if let Command::Assert { term } | Command::DefineFun { term, .. } = command {
                    assert!(!contains_binders(&term), "{} leaked {term}", file.display());
                }
            }
            for rule in plan.rules {
                assert!(
                    !contains_binders(&rule.body),
                    "{} leaked binder in rule {}",
                    file.display(),
                    rule.name
                );
            }
        }
    }

    #[test]
    fn existential_witness_depends_on_the_enclosing_universal() {
        let (_, plan) = lower_model(formula_model(
            "(forall ((x Bool)) (exists ((y Bool)) (= x y)))",
            "false",
        ))
        .unwrap();
        let exists = plan
            .rules
            .iter()
            .find(|rule| rule.kind == BinderKind::Exists)
            .unwrap();
        assert_eq!(exists.captures.len(), 1);
        let witness = exists.witness_instance(&[app("true", vec![])]).unwrap();
        assert!(witness
            .to_string()
            .contains(&format!("({} true)", exists.witnesses[0])));
        assert!(!contains_binders(&witness));
    }

    #[test]
    fn shadowed_binders_have_distinct_capture_free_names() {
        let (_, plan) = lower_model(formula_model(
            "(forall ((x Bool)) (and x (exists ((x Bool)) (not x))))",
            "false",
        ))
        .unwrap();
        let outer = plan
            .rules
            .iter()
            .find(|rule| rule.kind == BinderKind::Forall)
            .unwrap();
        let inner = plan
            .rules
            .iter()
            .find(|rule| rule.kind == BinderKind::Exists)
            .unwrap();
        assert_ne!(outer.variables[0].0, inner.variables[0].0);
        assert!(!inner
            .captures
            .iter()
            .any(|(symbol, _)| symbol == &outer.variables[0].0));
    }

    #[test]
    fn nested_constant_lambdas_use_nested_constant_arrays() {
        let source = model("(declare-fun a () (Array Bool (Array Bool Bool)))
            (define-fun init () Bool (! (= a (lambda ((x Bool)) (lambda ((y Bool)) false))) :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! true :invar-property 0))");
        let (lowered, plan) = lower_model(source).unwrap();
        assert!(plan.rules.is_empty());
        let (abstracted, types) = lowered.abstract_array_theory();
        assert!(types.contains(&("Bool".into(), "Bool".into())));
        assert!(types.contains(&("Bool".into(), "Array_Bool_Bool".into())));
        assert!(abstracted
            .as_vmt_string()
            .contains("(ConstArr_Bool_Array_Bool_Bool (ConstArr_Bool_Bool false))"));
    }

    #[test]
    fn quantifier_polarities_and_alternation_are_sound_over_booleans() {
        // These formulas are unsatisfiable; either polarity can require
        // universal instances as well as existential witnesses.
        for init in [
            "(forall ((x Bool)) x)",
            "(not (exists ((x Bool)) x))",
            "(exists ((x Bool)) (forall ((y Bool)) (= x y)))",
            "(not (forall ((x Bool)) (exists ((y Bool)) (= x y))))",
            "(= false (exists ((x Bool) (y Bool)) (distinct x y)))",
        ] {
            let result = check(init, "false").unwrap_or_else(|error| panic!("{init}: {error}"));
            assert!(!result.counterexample);
            assert_eq!(
                result
                    .solver_statistics
                    .get_f64("concrete_validation_checks"),
                Some(0.0)
            );
        }
        // Exhaustion is inconclusive. It must never prove these satisfiable
        // formulas inconsistent or delegate their quantifiers to Z3.
        for init in [
            "(exists ((x Bool)) x)",
            "(not (forall ((x Bool)) x))",
            "(forall ((x Bool)) (exists ((y Bool)) (= x y)))",
            "(exists ((x Bool)) (and x (forall ((x Bool)) (= x x))))",
        ] {
            assert!(
                matches!(
                    check(init, "false"),
                    Err(crate::Error::AbstractionExhausted { .. })
                ),
                "{init}"
            );
        }
    }
}
