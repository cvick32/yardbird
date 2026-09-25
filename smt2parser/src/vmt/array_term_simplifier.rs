//! Exact, theory-valid simplifications for native array terms.
//!
//! These rewrites run before array operations are replaced by uninterpreted
//! functions. A rewrite is admitted only when declarations and local bindings
//! prove that both operations are native array operations.

use std::collections::{HashMap, HashSet};

use crate::concrete::{Command, FunctionDec, Identifier, QualIdentifier, Sort, Symbol, Term};

type LocalSorts = HashMap<String, Option<Sort>>;
pub type AbstractedArrayCommands = (Vec<Command>, Vec<(String, String)>);

#[derive(Clone, Debug)]
struct FunctionSignature {
    parameters: Vec<Sort>,
    result: Sort,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NativeArrayOperation {
    Store,
}

#[derive(Clone, Debug)]
struct SimplifiedTerm {
    term: Term,
    sort: Option<Sort>,
    native_array_operation: Option<NativeArrayOperation>,
}

#[derive(Clone, Default)]
pub struct ArrayTermSimplifier {
    global_sorts: HashMap<String, Sort>,
    function_signatures: HashMap<String, FunctionSignature>,
    user_function_names: HashSet<String>,
    exact_read_after_write_rewrites: u64,
    abstraction: Option<super::array_abstractor::ArrayAbstractor>,
    skip_simplification: bool,
    abstraction_error: Option<String>,
}

impl ArrayTermSimplifier {
    pub fn from_commands(commands: &[Command]) -> Self {
        let mut simplifier = Self::default();
        for command in commands {
            match command {
                Command::DeclareConst { symbol, sort } => {
                    simplifier
                        .global_sorts
                        .insert(symbol.0.clone(), sort.clone());
                }
                Command::DeclareFun {
                    symbol,
                    parameters,
                    sort,
                } => simplifier.register_function(symbol, parameters, sort),
                Command::DefineFun { sig, .. } | Command::DefineFunRec { sig, .. } => {
                    simplifier.register_function_signature(sig);
                }
                Command::DefineFunsRec { funs } => {
                    for (sig, _) in funs {
                        simplifier.register_function_signature(sig);
                    }
                }
                _ => {}
            }
        }
        simplifier
    }

    /// Type-directed abstraction, including lexically scoped binder variables.
    /// Unknown array operand sorts are errors, never guessed as Int -> Int.
    pub fn abstract_commands(
        commands: &[Command],
        simplify: bool,
    ) -> Result<AbstractedArrayCommands, String> {
        let mut pass = Self::from_commands(commands);
        pass.abstraction = Some(super::array_abstractor::ArrayAbstractor::default());
        pass.skip_simplification = !simplify;
        let rewritten = commands
            .iter()
            .cloned()
            .map(|c| pass.simplify_command(c))
            .collect::<Vec<_>>();
        if let Some(error) = pass.abstraction_error {
            return Err(error);
        }
        let mut abstractor = pass.abstraction.take().unwrap();
        // Terms were rewritten using source sorts; now consistently rewrite all
        // annotations and declarations, including quantified variable sorts.
        struct Sorts<'a>(&'a mut super::array_abstractor::ArrayAbstractor);
        impl crate::rewriter::Rewriter for Sorts<'_> {
            type V = crate::concrete::SyntaxBuilder;
            type Error = crate::concrete::Error;
            fn visitor(&mut self) -> &mut Self::V {
                &mut self.0.visitor
            }
            fn process_sort(&mut self, sort: Sort) -> Result<Sort, Self::Error> {
                Ok(self.0.convert_sort_to_abstracted(&sort))
            }
        }
        let rewritten = rewritten
            .into_iter()
            .map(|c| {
                c.accept(&mut Sorts(&mut abstractor))
                    .map_err(|e| e.to_string())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let types = abstractor.sorted_array_types();
        let mut result = abstractor.get_array_type_definitions();
        // Quantifier lowering can already have declared these exact functions.
        // The preparation caller checks source-name collisions before lowering.
        for command in rewritten {
            let name = match &command {
                Command::DeclareFun { symbol, .. }
                | Command::DeclareSort { symbol, .. }
                | Command::DeclareConst { symbol, .. } => Some(&symbol.0),
                Command::DefineFun { sig, .. } | Command::DefineFunRec { sig, .. } => {
                    Some(&sig.name.0)
                }
                _ => None,
            };
            let duplicate = name.and_then(|name| {
                result.iter().find(|existing| match existing {
                    Command::DeclareFun { symbol, .. } | Command::DeclareSort { symbol, .. } => {
                        &symbol.0 == name
                    }
                    _ => false,
                })
            });
            match duplicate {
                Some(existing) if existing == &command => {}
                Some(_) => {
                    return Err(
                        "generated array declaration conflicts with an existing declaration".into(),
                    )
                }
                None => result.push(command),
            }
        }
        Ok((result, types))
    }

    pub fn exact_read_after_write_rewrites(&self) -> u64 {
        self.exact_read_after_write_rewrites
    }

    pub fn simplify_command(&mut self, command: Command) -> Command {
        match command {
            Command::Assert { term } => Command::Assert {
                term: self.simplify_term(term, &HashMap::new()).term,
            },
            Command::DefineFun { sig, term } => {
                let locals = parameter_sorts(&sig);
                Command::DefineFun {
                    sig,
                    term: self.simplify_term(term, &locals).term,
                }
            }
            Command::DefineFunRec { sig, term } => {
                let locals = parameter_sorts(&sig);
                Command::DefineFunRec {
                    sig,
                    term: self.simplify_term(term, &locals).term,
                }
            }
            Command::DefineFunsRec { funs } => Command::DefineFunsRec {
                funs: funs
                    .into_iter()
                    .map(|(sig, term)| {
                        let locals = parameter_sorts(&sig);
                        let term = self.simplify_term(term, &locals).term;
                        (sig, term)
                    })
                    .collect(),
            },
            Command::GetValue { terms } => Command::GetValue {
                terms: terms
                    .into_iter()
                    .map(|term| self.simplify_term(term, &HashMap::new()).term)
                    .collect(),
            },
            command => command,
        }
    }

    fn register_function(&mut self, symbol: &Symbol, parameters: &[Sort], result: &Sort) {
        self.user_function_names.insert(symbol.0.clone());
        self.function_signatures.insert(
            symbol.0.clone(),
            FunctionSignature {
                parameters: parameters.to_vec(),
                result: result.clone(),
            },
        );
        if parameters.is_empty() {
            self.global_sorts.insert(symbol.0.clone(), result.clone());
        }
    }

    fn register_function_signature(&mut self, sig: &FunctionDec<Symbol, Sort>) {
        let parameters = sig
            .parameters
            .iter()
            .map(|(_, sort)| sort.clone())
            .collect::<Vec<_>>();
        self.register_function(&sig.name, &parameters, &sig.result);
    }

    fn simplify_term(&mut self, term: Term, locals: &LocalSorts) -> SimplifiedTerm {
        match term {
            Term::Constant(constant) => SimplifiedTerm {
                term: Term::Constant(constant),
                sort: None,
                native_array_operation: None,
            },
            Term::QualIdentifier(identifier) => {
                let sort = match &identifier {
                    QualIdentifier::Sorted { sort, .. } => Some(sort.clone()),
                    QualIdentifier::Simple { .. } => {
                        let name = identifier.get_name();
                        match locals.get(&name) {
                            Some(sort) => sort.clone(),
                            None => self.global_sorts.get(&name).cloned(),
                        }
                    }
                };
                SimplifiedTerm {
                    term: Term::QualIdentifier(identifier),
                    sort,
                    native_array_operation: None,
                }
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let arguments = arguments
                    .into_iter()
                    .map(|argument| self.simplify_term(argument, locals))
                    .collect::<Vec<_>>();
                self.simplify_application(qual_identifier, arguments)
            }
            Term::Let { var_bindings, term } => {
                let mut body_locals = locals.clone();
                let var_bindings = var_bindings
                    .into_iter()
                    .map(|(symbol, value)| {
                        let value = self.simplify_term(value, locals);
                        body_locals.insert(symbol.0.clone(), value.sort.clone());
                        (symbol, value.term)
                    })
                    .collect();
                let body = self.simplify_term(*term, &body_locals);
                SimplifiedTerm {
                    term: Term::Let {
                        var_bindings,
                        term: Box::new(body.term),
                    },
                    sort: body.sort,
                    native_array_operation: None,
                }
            }
            Term::Lambda { vars, term } => {
                let mut body_locals = locals.clone();
                for (symbol, sort) in &vars {
                    body_locals.insert(symbol.0.clone(), Some(sort.clone()));
                }
                let body = self.simplify_term(*term, &body_locals);
                SimplifiedTerm {
                    term: Term::Lambda {
                        vars,
                        term: Box::new(body.term),
                    },
                    sort: None,
                    native_array_operation: None,
                }
            }
            Term::Forall { vars, term } => {
                let mut body_locals = locals.clone();
                for (symbol, sort) in &vars {
                    body_locals.insert(symbol.0.clone(), Some(sort.clone()));
                }
                let body = self.simplify_term(*term, &body_locals);
                SimplifiedTerm {
                    term: Term::Forall {
                        vars,
                        term: Box::new(body.term),
                    },
                    sort: None,
                    native_array_operation: None,
                }
            }
            Term::Exists { vars, term } => {
                let mut body_locals = locals.clone();
                for (symbol, sort) in &vars {
                    body_locals.insert(symbol.0.clone(), Some(sort.clone()));
                }
                let body = self.simplify_term(*term, &body_locals);
                SimplifiedTerm {
                    term: Term::Exists {
                        vars,
                        term: Box::new(body.term),
                    },
                    sort: None,
                    native_array_operation: None,
                }
            }
            Term::Match { term, cases } => {
                let matched = self.simplify_term(*term, locals);
                let mut result_sort = None;
                let cases = cases
                    .into_iter()
                    .map(|(symbols, case)| {
                        let mut case_locals = locals.clone();
                        for symbol in &symbols {
                            case_locals.insert(symbol.0.clone(), None);
                        }
                        let case = self.simplify_term(case, &case_locals);
                        if result_sort.is_none() {
                            result_sort = case.sort.clone();
                        }
                        (symbols, case.term)
                    })
                    .collect();
                SimplifiedTerm {
                    term: Term::Match {
                        term: Box::new(matched.term),
                        cases,
                    },
                    sort: result_sort,
                    native_array_operation: None,
                }
            }
            Term::Attributes { term, attributes } => {
                let inner = self.simplify_term(*term, locals);
                SimplifiedTerm {
                    term: Term::Attributes {
                        term: Box::new(inner.term),
                        attributes,
                    },
                    sort: inner.sort,
                    native_array_operation: inner.native_array_operation,
                }
            }
        }
    }

    fn simplify_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<SimplifiedTerm>,
    ) -> SimplifiedTerm {
        let name = qual_identifier.get_name();
        let is_unshadowed = !self.user_function_names.contains(&name);
        let is_native_select = is_simple_operator(&qual_identifier, "select")
            && arguments.len() == 2
            && is_unshadowed
            && arguments[0].sort.as_ref().is_some_and(is_array_sort);
        let is_native_store = is_simple_operator(&qual_identifier, "store")
            && arguments.len() == 3
            && is_unshadowed
            && arguments[0].sort.as_ref().is_some_and(is_array_sort);

        if !self.skip_simplification
            && is_native_select
            && arguments[0].native_array_operation == Some(NativeArrayOperation::Store)
        {
            if let Term::Application {
                arguments: store_arguments,
                ..
            } = &arguments[0].term
            {
                if store_arguments[1] == arguments[1].term {
                    self.exact_read_after_write_rewrites += 1;
                    return SimplifiedTerm {
                        term: store_arguments[2].clone(),
                        sort: arguments[0].sort.as_ref().and_then(array_value_sort),
                        native_array_operation: None,
                    };
                }
            }
        }

        let sort = if is_native_store {
            arguments[0].sort.clone()
        } else if is_native_select {
            arguments[0].sort.as_ref().and_then(array_value_sort)
        } else if name == "ite" && arguments.len() == 3 {
            arguments[1].sort.clone()
        } else if let QualIdentifier::Sorted { sort, .. } = &qual_identifier {
            Some(sort.clone())
        } else {
            self.function_signatures.get(&name).and_then(|signature| {
                (signature.parameters.len() == arguments.len()).then(|| signature.result.clone())
            })
        };
        let mut qual_identifier = qual_identifier;
        if let Some(abstractor) = &mut self.abstraction {
            let array_sort = if is_native_select || is_native_store {
                arguments[0].sort.as_ref()
            } else if name == "const" && is_unshadowed {
                sort.as_ref()
            } else {
                None
            };
            if let Some(array_sort @ Sort::Parameterized { parameters, .. }) = array_sort {
                if is_array_sort(array_sort) {
                    abstractor.convert_sort_to_abstracted(array_sort);
                    let op = if is_native_select {
                        "Read"
                    } else if is_native_store {
                        "Write"
                    } else {
                        "ConstArr"
                    };
                    qual_identifier = QualIdentifier::simple(format!(
                        "{}_{}_{}",
                        op,
                        abstractor.sort_to_string(&parameters[0]),
                        abstractor.sort_to_string(&parameters[1])
                    ));
                }
            } else if is_unshadowed && matches!(name.as_str(), "select" | "store" | "const") {
                self.abstraction_error = Some(format!("cannot determine array sort for {name}"));
            }
        }
        SimplifiedTerm {
            term: Term::Application {
                qual_identifier,
                arguments: arguments
                    .into_iter()
                    .map(|argument| argument.term)
                    .collect(),
            },
            sort,
            native_array_operation: is_native_store.then_some(NativeArrayOperation::Store),
        }
    }
}

fn parameter_sorts(sig: &FunctionDec<Symbol, Sort>) -> LocalSorts {
    sig.parameters
        .iter()
        .map(|(symbol, sort)| (symbol.0.clone(), Some(sort.clone())))
        .collect()
}

fn is_simple_operator(identifier: &QualIdentifier, expected: &str) -> bool {
    matches!(
        identifier,
        QualIdentifier::Simple {
            identifier: Identifier::Simple { symbol }
        } if symbol.0 == expected
    )
}

fn is_array_sort(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Parameterized {
            identifier,
            parameters,
        } if identifier.to_string() == "Array" && parameters.len() == 2
    )
}

fn array_value_sort(sort: &Sort) -> Option<Sort> {
    match sort {
        Sort::Parameterized {
            identifier,
            parameters,
        } if identifier.to_string() == "Array" && parameters.len() == 2 => {
            Some(parameters[1].clone())
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use crate::{concrete::SyntaxBuilder, CommandStream};

    use super::*;

    fn simplify(input: &[u8]) -> (Vec<Command>, u64) {
        let commands = CommandStream::new(Cursor::new(input), SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let mut simplifier = ArrayTermSimplifier::from_commands(&commands);
        let commands = commands
            .into_iter()
            .map(|command| simplifier.simplify_command(command))
            .collect();
        (commands, simplifier.exact_read_after_write_rewrites())
    }

    fn asserted_term(commands: &[Command]) -> &Term {
        commands
            .iter()
            .find_map(|command| match command {
                Command::Assert { term } => Some(term),
                _ => None,
            })
            .unwrap()
    }

    #[test]
    fn eliminates_exact_native_read_after_write() {
        let (commands, rewrites) = simplify(
            br#"
                (declare-const A (Array Int Int))
                (declare-const i Int)
                (declare-const v Int)
                (assert (= (select (store A i v) i) v))
            "#,
        );

        assert_eq!(asserted_term(&commands).to_string(), "(= v v)");
        assert_eq!(rewrites, 1);
    }

    #[test]
    fn does_not_rewrite_same_named_uninterpreted_functions() {
        let (commands, rewrites) = simplify(
            br#"
                (declare-sort Value 0)
                (declare-fun store (Value Int Value) Value)
                (declare-fun select (Value Int) Value)
                (declare-const A Value)
                (declare-const i Int)
                (declare-const v Value)
                (assert (= (select (store A i v) i) v))
            "#,
        );

        assert_eq!(
            asserted_term(&commands).to_string(),
            "(= (select (store A i v) i) v)"
        );
        assert_eq!(rewrites, 0);
    }

    #[test]
    fn local_bindings_cannot_inherit_a_shadowed_global_array_sort() {
        let (commands, rewrites) = simplify(
            br#"
                (declare-const A (Array Int Int))
                (declare-const i Int)
                (declare-const v Int)
                (assert (let ((A 0)) (= (select (store A i v) i) v)))
            "#,
        );

        assert_eq!(
            asserted_term(&commands).to_string(),
            "(let ((A 0)) (= (select (store A i v) i) v))"
        );
        assert_eq!(rewrites, 0);
    }

    #[test]
    fn leaves_different_indices_unchanged() {
        let (commands, rewrites) = simplify(
            br#"
                (declare-const A (Array Int Int))
                (declare-const i Int)
                (declare-const j Int)
                (declare-const v Int)
                (assert (select (store A i v) j))
            "#,
        );

        assert_eq!(
            asserted_term(&commands).to_string(),
            "(select (store A i v) j)"
        );
        assert_eq!(rewrites, 0);
    }

    #[test]
    fn simplifies_bottom_up_through_nested_stores() {
        let (commands, rewrites) = simplify(
            br#"
                (declare-const A (Array Int Int))
                (declare-const B (Array Int Int))
                (declare-const i Int)
                (declare-const j Int)
                (declare-const v Int)
                (declare-const w Int)
                (assert (= (select (store A i (select (store B j w) j)) i) w))
            "#,
        );

        assert_eq!(asserted_term(&commands).to_string(), "(= w w)");
        assert_eq!(rewrites, 2);
    }

    #[test]
    fn uses_exact_bitvector_index_syntax() {
        let (commands, rewrites) = simplify(
            br#"
                (declare-const A (Array (_ BitVec 8) Int))
                (declare-const v Int)
                (assert (= (select (store A #x0f v) #x0f) v))
            "#,
        );

        assert_eq!(asserted_term(&commands).to_string(), "(= v v)");
        assert_eq!(rewrites, 1);
    }

    #[test]
    fn simplifies_quantified_array_bodies() {
        let (commands, rewrites) = simplify(
            br#"
                (assert (forall ((A (Array Int Int)) (i Int) (v Int))
                    (= (select (store A i v) i) v)))
            "#,
        );

        assert_eq!(
            asserted_term(&commands).to_string(),
            "(forall ((A (Array Int Int)) (i Int) (v Int)) (= v v))"
        );
        assert_eq!(rewrites, 1);
    }

    #[test]
    fn simplifies_lambda_array_bodies() {
        let (commands, rewrites) = simplify(
            br#"
                (declare-const A (Array Int Int))
                (declare-const v Int)
                (assert (= (lambda ((i Int)) (select (store A i v) i))
                           (lambda ((i Int)) v)))
            "#,
        );

        assert_eq!(
            asserted_term(&commands).to_string(),
            "(= (lambda ((i Int)) v) (lambda ((i Int)) v))"
        );
        assert_eq!(rewrites, 1);
    }
}
