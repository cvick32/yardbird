use smt2parser::concrete::{Constant, SyntaxBuilder, Term};
use std::collections::HashMap;
use z3::{
    ast::{Ast, Bool, Dynamic},
    FuncDecl,
};

pub struct FunctionDefinition {
    z3_function: FuncDecl,
    domain: Vec<z3::Sort>,
}
impl FunctionDefinition {
    fn apply(&self, argument_values: Vec<Dynamic>) -> Dynamic {
        assert!(self.domain.len() == argument_values.len());
        self.z3_function.apply(
            argument_values
                .iter()
                .map(|x| x as _)
                .collect::<Vec<_>>()
                .as_slice(),
        )
    }

    fn new(arg_sorts: Vec<z3::Sort>, func_decl: FuncDecl) -> Self {
        Self {
            z3_function: func_decl,
            domain: arg_sorts,
        }
    }
}

pub struct Z3VarContext {
    pub builder: SyntaxBuilder,
    pub var_name_to_z3_term: HashMap<String, Dynamic>,
    pub function_name_to_z3_function: HashMap<String, FunctionDefinition>,
}

impl Z3VarContext {
    pub(crate) fn new() -> Self {
        Z3VarContext {
            builder: SyntaxBuilder,
            var_name_to_z3_term: HashMap::new(),
            function_name_to_z3_function: HashMap::new(),
        }
    }

    /// This is for the extra terms that we want to add to the egraph after the variable
    /// interpretations and Array function interpretations.
    pub(crate) fn rewrite_term(&self, outer_term: &smt2parser::concrete::Term) -> Dynamic {
        match outer_term {
            Term::Constant(constant) => match constant {
                Constant::Numeral(big_uint) => {
                    z3::ast::Int::from_u64(big_uint.try_into().unwrap()).into()
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
                    z3::ast::Bool::from_bool(true).into()
                } else if var_name == "false" {
                    z3::ast::Bool::from_bool(false).into()
                } else {
                    panic!("Could not find symbol {var_name} in Z3VarContext.");
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
                    let var: Dynamic = if self.var_name_to_z3_term.contains_key(&symbol.0) {
                        self.var_name_to_z3_term.get(&symbol.0).unwrap().clone()
                    } else {
                        panic!("Unknown quantified variable {symbol} encountered!")
                    };
                    bounds.push(var);
                }
                let quantified_term = self.rewrite_term(term).as_bool().unwrap();
                // Convert to references with trait object cast for z3::ast::forall_const
                let bound_refs: Vec<&dyn Ast> = bounds.iter().map(|d| d as &dyn Ast).collect();
                z3::ast::forall_const(&bound_refs, &[], &quantified_term).into()
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

    #[allow(clippy::only_used_in_recursion)]
    fn get_z3_sort(&self, smt2_sort: &smt2parser::concrete::Sort) -> z3::Sort {
        match smt2_sort {
            smt2parser::concrete::Sort::Simple { identifier } => match identifier {
                smt2parser::concrete::Identifier::Simple { symbol } => match symbol.0.as_str() {
                    "Bool" => z3::Sort::bool(),
                    "Int" => z3::Sort::int(),
                    _ => z3::Sort::uninterpreted(z3::Symbol::String(symbol.0.clone())),
                },
                smt2parser::concrete::Identifier::Indexed { symbol, indices } => {
                    // Handle indexed sorts like (_ BitVec 32)
                    if symbol.0 == "BitVec" {
                        // Extract the bit width from the indices
                        if let Some(smt2parser::visitors::Index::Numeral(width)) = indices.first() {
                            // Convert BigUint to u32 by parsing through string
                            // (simpler than dealing with num crate conversions)
                            let width_str = width.to_string();
                            let width_u32: u32 =
                                width_str.parse().expect("BitVec width must be a valid u32");
                            z3::Sort::bitvector(width_u32)
                        } else {
                            panic!("BitVec sort must have a numeral width");
                        }
                    } else {
                        todo!("Must implement indexed sort: {}", symbol)
                    }
                }
            },
            smt2parser::concrete::Sort::Parameterized {
                identifier,
                parameters,
            } => match identifier {
                smt2parser::concrete::Identifier::Simple { symbol } => {
                    if symbol.0 == "Array" {
                        z3::Sort::array(
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
    fn call_z3_function(&self, function_name: String, argument_values: Vec<Dynamic>) -> Dynamic {
        if function_name == "+" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            let int_ref_args = args.iter().collect::<Vec<_>>();
            z3::ast::Int::add(&int_ref_args).into()
        } else if function_name == "-" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            let int_ref_args = args.iter().collect::<Vec<_>>();
            if args.len() == 1 {
                z3::ast::Int::unary_minus(int_ref_args[0]).into()
            } else {
                z3::ast::Int::sub(&int_ref_args).into()
            }
        } else if function_name == "*" {
            let args = argument_values
                .iter()
                .map(|x| x.as_int().expect("Not an int"))
                .collect::<Vec<_>>();
            let int_ref_args = args.iter().collect::<Vec<_>>();
            z3::ast::Int::mul(&int_ref_args).into()
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
            argument_values[0].eq(&argument_values[1]).into()
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
            z3::ast::Bool::and(&ref_args).into()
        } else if function_name == "or" {
            let args = argument_values
                .iter()
                .map(|x| x.as_bool().expect("Not a bool"))
                .collect::<Vec<_>>();
            let ref_args = args.iter().collect::<Vec<_>>();
            z3::ast::Bool::or(&ref_args).into()
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
        } else if function_name == "const" {
            let sort = match argument_values[0].sort_kind() {
                z3::SortKind::Int => z3::Sort::int(),
                _ => todo!("Add Z3 array value: {:?}", argument_values[0].sort_kind()),
            };
            z3::ast::Array::const_array(&sort, &argument_values[0]).into()
        } else {
            todo!("Add Z3 function: ({function_name} {argument_values:?})");
        }
    }

    pub(crate) fn make_and(&self, all_z3_insts: Vec<Bool>) -> z3::ast::Bool {
        let inst_ref_args = all_z3_insts.iter().collect::<Vec<_>>();
        z3::ast::Bool::and(&inst_ref_args)
    }

    pub fn create_variable(
        &mut self,
        symbol: &smt2parser::concrete::Symbol,
        sort: &smt2parser::concrete::Sort,
    ) {
        let var_sort = self.get_z3_sort(sort);
        let var_func_decl = FuncDecl::new(symbol.0.clone(), &[], &var_sort);
        let var_dynamic = var_func_decl.apply(&[]);
        let var_var_name = symbol.0.clone();
        self.var_name_to_z3_term
            .insert(var_var_name, var_dynamic.clone());
    }

    pub(crate) fn get_interpretation(&self, model: &z3::Model, z3_term: &Dynamic) -> Dynamic {
        model
            .eval(z3_term, true) // Add Model completion so we don't have to deal with ite in the interpretations.
            .unwrap_or_else(|| panic!("Term not found in model: {z3_term}"))
    }
}

impl smt2parser::rewriter::Rewriter for Z3VarContext {
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
            let func_decl = FuncDecl::new(symbol.0.clone(), &sort_refs, &return_sort);
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
