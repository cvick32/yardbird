//! Closure conversion and sort checking for binders and array lambdas.
use super::*;
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

pub(super) fn sort_name(sort: &Sort) -> String {
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
        _ => TermLanguage::sort_to_name(sort),
    }
}

pub(crate) fn abstract_sort(sort: &Sort) -> Sort {
    match sort {
        Sort::Parameterized { identifier, .. } if identifier.to_string() == "Array" => {
            string_to_sort(&sort_name(sort))
        }
        _ => sort.clone(),
    }
}

struct Lowerer<'a> {
    provenance: &'a mut crate::theories::quantifiers::provenance::QuantifierProvenance,
    signatures: HashMap<String, (Vec<Sort>, Sort)>,
    reserved: HashSet<String>,
    next_id: usize,
    declarations: Vec<Command>,
    rules: Vec<BinderRule>,
    native_binders: HashMap<String, Term>,
    retain_native_binders: bool,
}

pub(crate) fn term_sort(
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
                .get(&name)
                .or_else(|| signatures.get(&base))
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

impl Lowerer<'_> {
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
        let source_id = self.provenance.source_for_variables(&vars);
        let scoped_variables = source_id.as_ref().map(|_| vars.clone()).unwrap_or_default();
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
        let native_body = substitute(body, renaming);
        let native = self.retain_native_binders.then(|| match kind {
            BinderKind::Forall => Term::Forall {
                vars: variables.clone(),
                term: Box::new(native_body.clone()),
            },
            BinderKind::Exists => Term::Exists {
                vars: variables.clone(),
                term: Box::new(native_body.clone()),
            },
            BinderKind::Lambda => Term::Lambda {
                vars: variables.clone(),
                term: Box::new(native_body.clone()),
            },
        });
        let body = self.lower(native_body, &inner)?;
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
                if let Some(id) = &source_id {
                    self.provenance
                        .sources
                        .get_mut(id)
                        .unwrap()
                        .eliminated_as_constant_array = true;
                }
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
        let unit_capture = captures.is_empty();
        if unit_capture {
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
        log::info!(
            "Quantified rule {name} ({kind:?}):\n  captures: {}\n  variables: {}\n  body: {body}\n  witnesses: {}",
            captures
                .iter()
                .map(|(symbol, sort)| format!("({symbol} {sort})"))
                .collect::<Vec<_>>()
                .join(" "),
            variables
                .iter()
                .map(|(symbol, sort)| format!("({symbol} {sort})"))
                .collect::<Vec<_>>()
                .join(" "),
            witnesses.join(" "),
        );
        if let Some(source_id) = source_id {
            use crate::theories::quantifiers::provenance::{LoweredQuantifier, LoweredVariable};
            self.provenance.rules.insert(
                QuantifiedRule::input_binder(&name).name().into(),
                LoweredQuantifier {
                    source_id,
                    helper: name.clone(),
                    kind: format!("{kind:?}").to_lowercase(),
                    variables: scoped_variables
                        .iter()
                        .zip(&variables)
                        .map(|((scoped, _), (lowered, _))| LoweredVariable {
                            scoped_name: scoped.0.clone(),
                            lowered_name: lowered.0.clone(),
                        })
                        .collect(),
                    captures: captures
                        .iter()
                        .map(|(s, t)| (s.to_string(), t.to_string()))
                        .collect(),
                    witnesses: witnesses.clone(),
                    lowered_body: body.to_string(),
                },
            );
        }
        if let Some(native) = native {
            self.native_binders.insert(name.clone(), native);
        }
        self.rules.push(BinderRule {
            name: name.clone(),
            kind,
            captures,
            variables,
            body,
            witnesses,
            result_sort,
            unit_capture,
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

/// Lower every binder before array abstraction, including helper definitions
/// and background assertions. The returned model contains no binder terms.
#[cfg(test)]
pub(crate) fn lower_model(model: VMTModel) -> anyhow::Result<(VMTModel, QuantifierPlan)> {
    lower_model_with_provenance(model, &mut Default::default())
}

pub(crate) fn lower_model_with_provenance(
    model: VMTModel,
    provenance: &mut crate::theories::quantifiers::provenance::QuantifierProvenance,
) -> anyhow::Result<(VMTModel, QuantifierPlan)> {
    lower_model_for_eager(model, provenance, false)
}

pub(super) fn lower_model_for_eager(
    model: VMTModel,
    provenance: &mut crate::theories::quantifiers::provenance::QuantifierProvenance,
    retain_native_binders: bool,
) -> anyhow::Result<(VMTModel, QuantifierPlan)> {
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
        provenance,
        signatures,
        reserved,
        next_id: 0,
        declarations: vec![],
        rules: vec![],
        native_binders: HashMap::new(),
        retain_native_binders,
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
            native_binders: lowerer.native_binders,
            signatures,
            seeds,
            compiled: Default::default(),
        },
    ))
}
