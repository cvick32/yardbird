use smt2parser::{
    concrete::{Constant, SyntaxBuilder, Term},
    vmt::smt::SMTProblem,
};
use std::collections::HashMap;
use z3::{ast::Dynamic, Context, FuncDecl};

pub struct FunctionDefinition<'ctx> {
    z3_function: FuncDecl<'ctx>,
    domain: Vec<z3::Sort<'ctx>>,
}
impl<'ctx> FunctionDefinition<'ctx> {
    fn apply(&self, argument_values: Vec<Dynamic<'ctx>>) -> Dynamic<'_> {
        assert!(self.domain.len() == argument_values.len());
        self.z3_function.apply(
            argument_values
                .iter()
                .map(|x| x as _)
                .collect::<Vec<_>>()
                .as_slice(),
        )
    }

    fn new(arg_sorts: Vec<z3::Sort<'ctx>>, func_decl: FuncDecl<'ctx>) -> Self {
        Self {
            z3_function: func_decl,
            domain: arg_sorts,
        }
    }
}

pub struct Z3VarContext<'ctx> {
    pub builder: SyntaxBuilder,
    pub context: &'ctx Context,
    pub var_name_to_z3_term: HashMap<String, Dynamic<'ctx>>,
    pub function_name_to_z3_function: HashMap<String, FunctionDefinition<'ctx>>,
}

impl<'ctx> Z3VarContext<'ctx> {
    pub fn from(context: &'ctx Context, smt: &SMTProblem) -> Self {
        let mut var_context = Z3VarContext {
            builder: SyntaxBuilder,
            context,
            var_name_to_z3_term: HashMap::new(),
            function_name_to_z3_function: HashMap::new(),
        };
        for var_def in smt.get_variable_definitions() {
            let _ = var_def.accept(&mut var_context);
        }
        for function_def in smt.get_function_definitions() {
            let _ = function_def.accept(&mut var_context);
        }
        var_context
    }

    /// This is for the extra terms that we want to add to the egraph after the variable
    /// interpretations and Array function interpretations.
    pub(crate) fn rewrite_term(&'ctx self, term: &smt2parser::concrete::Term) -> Dynamic<'ctx> {
        let dd: Dynamic = match term {
            Term::Constant(constant) => match constant {
                Constant::Numeral(big_uint) => {
                    z3::ast::Int::from_u64(self.context, big_uint.try_into().unwrap()).into()
                }
                Constant::Decimal(_) => todo!(),
                Constant::Hexadecimal(_) => todo!(),
                Constant::Binary(_) => todo!(),
                Constant::String(_) => todo!(),
            },
            Term::QualIdentifier(symbol) => {
                let var_name = symbol.get_name();
                if self.var_name_to_z3_term.contains_key(&var_name) {
                    self.var_name_to_z3_term.get(&var_name).unwrap().clone()
                } else {
                    panic!()
                }
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let argument_values = arguments
                    .iter()
                    .map(|arg| self.rewrite_term(arg))
                    .collect::<Vec<_>>();

                let function_name = qual_identifier.get_name();

                if self
                    .function_name_to_z3_function
                    .contains_key(&function_name)
                {
                    let function_definition = self
                        .function_name_to_z3_function
                        .get(&function_name)
                        .unwrap();
                    function_definition.apply(argument_values)
                } else {
                    self.call_z3_function(function_name, argument_values)
                }
            }
            Term::Let {
                var_bindings: _,
                term: _,
            } => todo!(),
            Term::Forall { vars: _, term: _ } => todo!(),
            Term::Exists { vars: _, term: _ } => todo!(),
            Term::Match { term: _, cases: _ } => todo!(),
            Term::Attributes {
                term: _,
                attributes: _,
            } => todo!(),
        };
        dd
    }

    fn get_z3_sort(&self, smt2_sort: &smt2parser::concrete::Sort) -> z3::Sort<'ctx> {
        match smt2_sort {
            smt2parser::concrete::Sort::Simple { identifier } => match identifier {
                smt2parser::concrete::Identifier::Simple { symbol } => match symbol.0.as_str() {
                    "Bool" => z3::Sort::bool(self.context),
                    "Int" => z3::Sort::int(self.context),
                    _ => {
                        z3::Sort::uninterpreted(self.context, z3::Symbol::String(symbol.0.clone()))
                    }
                },
                smt2parser::concrete::Identifier::Indexed { symbol, indices: _ } => {
                    todo!("Must implement indexed sort: {}", symbol)
                }
            },
            smt2parser::concrete::Sort::Parameterized {
                identifier,
                parameters,
            } => match identifier {
                smt2parser::concrete::Identifier::Simple { symbol } => {
                    if symbol.0 == "Array" {
                        z3::Sort::array(
                            self.context,
                            &self.get_z3_sort(&parameters[0].clone()),
                            &self.get_z3_sort(&parameters[1].clone()),
                        )
                    } else {
                        todo!()
                    }
                }
                smt2parser::concrete::Identifier::Indexed {
                    symbol: _,
                    indices: _,
                } => todo!(),
            },
        }
    }

    /// Builds and calls the Z3 function corresponding to `function_name`. Returns
    /// the application of the function with the given arguments.
    fn call_z3_function(
        &self,
        function_name: String,
        argument_values: Vec<Dynamic<'ctx>>,
    ) -> Dynamic<'_> {
        if function_name == "+" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().unwrap())
                .collect::<Vec<_>>();
            let int_ref_args = args.iter().collect::<Vec<_>>();
            z3::ast::Int::add(self.context, &int_ref_args).into()
        } else if function_name == "-" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().unwrap())
                .collect::<Vec<_>>();
            let int_ref_args = args.iter().collect::<Vec<_>>();
            z3::ast::Int::sub(self.context, &int_ref_args).into()
        } else if function_name == "*" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().unwrap())
                .collect::<Vec<_>>();
            let int_ref_args = args.iter().collect::<Vec<_>>();
            z3::ast::Int::mul(self.context, &int_ref_args).into()
        } else if function_name == "mod" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().unwrap())
                .collect::<Vec<_>>();
            z3::ast::Int::modulo(&args[0], &args[1]).into()
        } else {
            todo!("Add Z3 function: {function_name}");
        }
    }
}

impl smt2parser::rewriter::Rewriter for Z3VarContext<'_> {
    type V = SyntaxBuilder;
    type Error = smt2parser::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.builder
    }

    fn visit_declare_fun(
        &mut self,
        symbol: <Self::V as smt2parser::visitors::Smt2Visitor>::Symbol,
        parameters: Vec<<Self::V as smt2parser::visitors::Smt2Visitor>::Sort>,
        sort: <Self::V as smt2parser::visitors::Smt2Visitor>::Sort,
    ) -> Result<<Self::V as smt2parser::visitors::Smt2Visitor>::Command, Self::Error> {
        let sort_binding = sort.clone();
        let var_sort = self.get_z3_sort(&sort_binding);
        if parameters.is_empty() {
            // Create Z3 object for variable.
            let var_func_decl = FuncDecl::new(self.context, symbol.0.clone(), &[], &var_sort);
            let var_dynamic = var_func_decl.apply(&[]);
            let var_var_name = symbol.0.clone();
            self.var_name_to_z3_term.insert(var_var_name, var_dynamic);
        } else {
            // Create Z3 object for function.
            let arg_sorts = parameters
                .iter()
                .map(|arg_sort| self.get_z3_sort(arg_sort))
                .collect::<Vec<z3::Sort>>();
            let sort_refs = arg_sorts.iter().collect::<Vec<&z3::Sort>>();
            let func_decl = FuncDecl::new(self.context, symbol.0.clone(), &sort_refs, &var_sort);
            self.function_name_to_z3_function.insert(
                symbol.0.clone(),
                FunctionDefinition::new(arg_sorts, func_decl),
            );
        }
        Ok(smt2parser::concrete::Command::DeclareFun {
            symbol,
            parameters,
            sort,
        })
    }
}
