use smt2parser::concrete::{Constant, SyntaxBuilder, Term};
use std::collections::HashMap;
use z3::{
    ast::{Ast, Bool, Dynamic},
    Context, FuncDecl,
};

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
    pub(crate) fn new(context: &'ctx Context) -> Self {
        Z3VarContext {
            builder: SyntaxBuilder,
            context,
            var_name_to_z3_term: HashMap::new(),
            function_name_to_z3_function: HashMap::new(),
        }
    }

    /// This is for the extra terms that we want to add to the egraph after the variable
    /// interpretations and Array function interpretations.
    pub(crate) fn rewrite_term(
        &'ctx self,
        outer_term: &smt2parser::concrete::Term,
    ) -> Dynamic<'ctx> {
        match outer_term {
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
                } else if var_name == "true" {
                    z3::ast::Bool::from_bool(self.context, true).into()
                } else if var_name == "false" {
                    z3::ast::Bool::from_bool(self.context, false).into()
                } else {
                    panic!("Could not find symbol {} in Z3VarContext.", var_name);
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
            Term::Forall { vars, term } => {
                let mut bounds = vec![];
                for (symbol, _) in vars {
                    let var: Dynamic<'_> = if self.var_name_to_z3_term.contains_key(&symbol.0) {
                        self.var_name_to_z3_term.get(&symbol.0).unwrap().clone()
                    } else {
                        panic!("Unknown quantified variable {symbol} encountered!")
                    };
                    bounds.push(var);
                }
                let quantified_term = self.rewrite_term(term).as_bool().unwrap();
                if bounds.len() == 1 {
                    z3::ast::forall_const(self.context, &[&bounds[0]], &[], &quantified_term).into()
                } else if bounds.len() == 2 {
                    z3::ast::forall_const(
                        self.context,
                        &[&bounds[0], &bounds[1]],
                        &[],
                        &quantified_term,
                    )
                    .into()
                } else {
                    todo!("Haven't implemented universal quantification for more than 2 variables.")
                }
            }
            Term::Let {
                var_bindings: _,
                term: _,
            } => todo!(),
            Term::Exists { vars: _, term: _ } => todo!(),
            Term::Match { term: _, cases: _ } => todo!(),
            Term::Attributes {
                term: _,
                attributes: _,
            } => todo!(),
        }
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
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            let int_ref_args = args.iter().collect::<Vec<_>>();
            z3::ast::Int::add(self.context, &int_ref_args).into()
        } else if function_name == "-" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            let int_ref_args = args.iter().collect::<Vec<_>>();
            if args.len() == 1 {
                z3::ast::Int::unary_minus(int_ref_args[0]).into()
            } else {
                z3::ast::Int::sub(self.context, &int_ref_args).into()
            }
        } else if function_name == "*" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            let int_ref_args = args.iter().collect::<Vec<_>>();
            z3::ast::Int::mul(self.context, &int_ref_args).into()
        } else if function_name == "/" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            z3::ast::Int::div(&args[0], &args[1]).into()
        } else if function_name == "mod" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            z3::ast::Int::modulo(&args[0], &args[1]).into()
        } else if function_name == "<=" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            z3::ast::Int::le(&args[0], &args[1]).into()
        } else if function_name == "<" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            z3::ast::Int::lt(&args[0], &args[1]).into()
        } else if function_name == ">=" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            z3::ast::Int::ge(&args[0], &args[1]).into()
        } else if function_name == ">" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            z3::ast::Int::gt(&args[0], &args[1]).into()
        } else if function_name == "=" {
            argument_values[0]._eq(&argument_values[1]).into()
        } else if function_name == "=>" {
            let args = argument_values
                .iter()
                .map(|x| x.as_bool().expect("Not a bool"))
                .collect::<Vec<_>>();
            z3::ast::Bool::implies(&args[0], &args[1]).into()
        } else if function_name == "and" {
            let args = argument_values
                .iter()
                .map(|x| x.as_bool().expect("Not a bool"))
                .collect::<Vec<_>>();
            let ref_args = args.iter().collect::<Vec<_>>();
            z3::ast::Bool::and(self.context, &ref_args).into()
        } else if function_name == "or" {
            let args = argument_values
                .iter()
                .map(|x| x.as_bool().expect("Not a bool"))
                .collect::<Vec<_>>();
            let ref_args = args.iter().collect::<Vec<_>>();
            z3::ast::Bool::or(self.context, &ref_args).into()
        } else if function_name == "ite" {
            let args = argument_values
                .iter()
                .map(|x| x.as_bool().expect("Not a bool"))
                .collect::<Vec<_>>();
            args[0].ite(&args[1], &args[2]).into()
        } else if function_name == "not" {
            let args = argument_values
                .iter()
                .map(|x| x.as_bool().expect("Not a bool"))
                .collect::<Vec<_>>();
            z3::ast::Bool::not(&args[0]).into()
        } else if function_name == "select" {
            let arr = argument_values[0].as_array().expect("Not an array");
            let idx = argument_values[1].clone();
            z3::ast::Array::select(&arr, &idx)
        } else if function_name == "store" {
            let arr = argument_values[0].as_array().expect("Not an array");
            let idx = argument_values[1].clone();
            let val = argument_values[2].clone();
            z3::ast::Array::store(&arr, &idx, &val).into()
        } else {
            todo!("Add Z3 function: {function_name}");
        }
    }

    pub(crate) fn make_and(&self, all_z3_insts: Vec<Bool<'ctx>>) -> z3::ast::Bool<'_> {
        let inst_ref_args = all_z3_insts.iter().collect::<Vec<_>>();
        z3::ast::Bool::and(self.context, &inst_ref_args)
    }

    pub fn create_variable(
        &mut self,
        symbol: &smt2parser::concrete::Symbol,
        sort: &smt2parser::concrete::Sort,
    ) {
        let var_sort = self.get_z3_sort(sort);
        let var_func_decl = FuncDecl::new(self.context, symbol.0.clone(), &[], &var_sort);
        let var_dynamic = var_func_decl.apply(&[]);
        let var_var_name = symbol.0.clone();
        self.var_name_to_z3_term
            .insert(var_var_name, var_dynamic.clone());
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
        if parameters.is_empty() {
            // Create Z3 object for variable.
            self.create_variable(&symbol, &sort);
        } else {
            // Create Z3 object for function.
            let arg_sorts = parameters
                .iter()
                .map(|arg_sort| self.get_z3_sort(arg_sort))
                .collect::<Vec<z3::Sort>>();
            let return_sort = self.get_z3_sort(&sort);
            let sort_refs = arg_sorts.iter().collect::<Vec<&z3::Sort>>();
            let func_decl = FuncDecl::new(self.context, symbol.0.clone(), &sort_refs, &return_sort);
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
