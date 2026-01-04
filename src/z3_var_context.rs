use smt2parser::concrete::{Constant, SyntaxBuilder, Term};
use smt2parser::concrete::{Identifier, QualIdentifier};
use std::cell::RefCell;
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
    pub var_name_to_z3_term: RefCell<HashMap<String, Dynamic>>,
    pub function_name_to_z3_function: HashMap<String, FunctionDefinition>,
}

impl Z3VarContext {
    pub(crate) fn new() -> Self {
        Z3VarContext {
            builder: SyntaxBuilder,
            var_name_to_z3_term: RefCell::new(HashMap::new()),
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
                Constant::Hexadecimal(hex_bytes) => {
                    let bit_width = (hex_bytes.len() * 4) as u32;
                    // Convert hex digits to u64 (big-endian interpretation)
                    let mut value: u64 = 0;
                    for &hex_digit in hex_bytes.iter() {
                        value = (value << 4) | (hex_digit as u64);
                    }
                    z3::ast::BV::from_u64(value, bit_width).into()
                }
                Constant::Binary(_) => todo!(),
                Constant::String(_) => todo!(),
            },
            Term::QualIdentifier(qual_id) => {
                use smt2parser::concrete::{Identifier, QualIdentifier};
                // Check if this is an indexed identifier like (_ bv0 1)
                match qual_id {
                    QualIdentifier::Simple { identifier } => match identifier {
                        Identifier::Indexed { symbol, indices } => {
                            if symbol.0.starts_with("bv") {
                                let value_str = &symbol.0[2..]; // Skip "bv" prefix
                                if let Some(smt2parser::visitors::Index::Numeral(width)) =
                                    indices.first()
                                {
                                    let width_str = width.to_string();
                                    let bit_width: u32 = width_str
                                        .parse()
                                        .expect("BitVec width must be a valid u32");
                                    if let Ok(value) = value_str.parse::<u64>() {
                                        z3::ast::BV::from_u64(value, bit_width).into()
                                    } else {
                                        // For larger values, use Z3's from_str which accepts a decimal string
                                        z3::ast::BV::from_str(bit_width, value_str)
                                            .unwrap_or_else(|| {
                                                panic!(
                                                    "Failed to parse bitvector value from {}",
                                                    value_str
                                                )
                                            })
                                            .into()
                                    }
                                } else {
                                    panic!("BitVec literal must have a numeral width");
                                }
                            } else {
                                let var_name = symbol.0.clone();
                                let vars = self.var_name_to_z3_term.borrow();
                                if vars.contains_key(&var_name) {
                                    vars.get(&var_name).unwrap().clone()
                                } else {
                                    panic!(
                                        "Could not find indexed identifier {} in Z3VarContext.",
                                        var_name
                                    );
                                }
                            }
                        }
                        Identifier::Simple { symbol } => {
                            let var_name = &symbol.0;
                            let vars = self.var_name_to_z3_term.borrow();
                            if vars.contains_key(var_name) {
                                vars.get(var_name).unwrap().clone()
                            } else if var_name == "true" {
                                z3::ast::Bool::from_bool(true).into()
                            } else if var_name == "false" {
                                z3::ast::Bool::from_bool(false).into()
                            } else {
                                panic!("Could not find symbol {} in Z3VarContext.", var_name);
                            }
                        }
                    },
                    QualIdentifier::Sorted {
                        identifier,
                        sort: _,
                    } => {
                        // For sorted identifiers, just get the base symbol name
                        let var_name = match identifier {
                            Identifier::Simple { symbol } => &symbol.0,
                            Identifier::Indexed { symbol, indices: _ } => &symbol.0,
                        };
                        let vars = self.var_name_to_z3_term.borrow();
                        if vars.contains_key(var_name) {
                            vars.get(var_name).unwrap().clone()
                        } else {
                            panic!(
                                "Could not find sorted identifier {} in Z3VarContext.",
                                var_name
                            );
                        }
                    }
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

                match qual_identifier {
                    QualIdentifier::Simple { identifier } => match identifier {
                        Identifier::Indexed { symbol, indices } => {
                            self.call_indexed_z3_function(&symbol.0, indices, argument_values)
                        }
                        Identifier::Simple { symbol } => {
                            let function_name = &symbol.0;

                            if self
                                .function_name_to_z3_function
                                .contains_key(function_name)
                            {
                                let function_definition = self
                                    .function_name_to_z3_function
                                    .get(function_name)
                                    .unwrap();
                                function_definition.apply(argument_values)
                            } else {
                                self.call_z3_function(function_name.clone(), argument_values)
                            }
                        }
                    },
                    QualIdentifier::Sorted {
                        identifier,
                        sort: _,
                    } => {
                        // For sorted identifiers, use the base symbol
                        let function_name = match identifier {
                            Identifier::Simple { symbol } => &symbol.0,
                            Identifier::Indexed { symbol, indices: _ } => &symbol.0,
                        };

                        if self
                            .function_name_to_z3_function
                            .contains_key(function_name)
                        {
                            let function_definition = self
                                .function_name_to_z3_function
                                .get(function_name)
                                .unwrap();
                            function_definition.apply(argument_values)
                        } else {
                            self.call_z3_function(function_name.clone(), argument_values)
                        }
                    }
                }
            }
            Term::Forall { vars, term } => {
                let mut bounds = vec![];
                let mut shadowed_vars = Vec::new();

                for (symbol, sort) in vars {
                    {
                        let var_map = self.var_name_to_z3_term.borrow();
                        if let Some(old_var) = var_map.get(&symbol.0) {
                            shadowed_vars.push((symbol.0.clone(), old_var.clone()));
                        }
                    }
                    // Create a fresh Z3 variable for this quantified variable
                    let var_sort = self.get_z3_sort(sort);
                    let var_func_decl = FuncDecl::new(symbol.0.clone(), &[], &var_sort);
                    let var_dynamic = var_func_decl.apply(&[]);
                    self.var_name_to_z3_term
                        .borrow_mut()
                        .insert(symbol.0.clone(), var_dynamic.clone());
                    bounds.push(var_dynamic);
                }

                let quantified_term = self.rewrite_term(term).as_bool().unwrap();

                {
                    let mut var_map = self.var_name_to_z3_term.borrow_mut();
                    // Restore shadowed variables
                    for (symbol, old_var) in shadowed_vars.iter() {
                        var_map.insert(symbol.clone(), old_var.clone());
                    }
                    for (symbol, _) in vars {
                        if !shadowed_vars.iter().any(|(s, _)| s == &symbol.0) {
                            var_map.remove(&symbol.0);
                        }
                    }
                }

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
            let condition = argument_values[0]
                .as_bool()
                .expect("ite condition must be bool");
            let then_val = &argument_values[1];
            let else_val = &argument_values[2];
            condition.ite(then_val, else_val)
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
        } else if function_name == "concat" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("concat arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("concat arg 2 must be bitvector");
            z3::ast::BV::concat(&bv1, &bv2).into()
        } else if function_name == "bvule" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvule arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvule arg 2 must be bitvector");
            z3::ast::BV::bvule(&bv1, &bv2).into()
        } else if function_name == "bvult" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvult arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvult arg 2 must be bitvector");
            z3::ast::BV::bvult(&bv1, &bv2).into()
        } else if function_name == "bvuge" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvuge arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvuge arg 2 must be bitvector");
            z3::ast::BV::bvuge(&bv1, &bv2).into()
        } else if function_name == "bvugt" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvugt arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvugt arg 2 must be bitvector");
            z3::ast::BV::bvugt(&bv1, &bv2).into()
        } else if function_name == "bvsle" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvsle arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvsle arg 2 must be bitvector");
            z3::ast::BV::bvsle(&bv1, &bv2).into()
        } else if function_name == "bvslt" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvslt arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvslt arg 2 must be bitvector");
            z3::ast::BV::bvslt(&bv1, &bv2).into()
        } else if function_name == "bvsge" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvsge arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvsge arg 2 must be bitvector");
            z3::ast::BV::bvsge(&bv1, &bv2).into()
        } else if function_name == "bvsgt" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvsgt arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvsgt arg 2 must be bitvector");
            z3::ast::BV::bvsgt(&bv1, &bv2).into()
        } else if function_name == "bvadd" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvadd arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvadd arg 2 must be bitvector");
            z3::ast::BV::bvadd(&bv1, &bv2).into()
        } else if function_name == "bvsub" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvsub arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvsub arg 2 must be bitvector");
            z3::ast::BV::bvsub(&bv1, &bv2).into()
        } else if function_name == "bvmul" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvmul arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvmul arg 2 must be bitvector");
            z3::ast::BV::bvmul(&bv1, &bv2).into()
        } else if function_name == "bvand" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvand arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvand arg 2 must be bitvector");
            z3::ast::BV::bvand(&bv1, &bv2).into()
        } else if function_name == "bvor" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvor arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvor arg 2 must be bitvector");
            z3::ast::BV::bvor(&bv1, &bv2).into()
        } else if function_name == "bvxor" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvxor arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvxor arg 2 must be bitvector");
            z3::ast::BV::bvxor(&bv1, &bv2).into()
        } else if function_name == "bvnot" {
            let bv = argument_values[0]
                .as_bv()
                .expect("bvnot arg must be bitvector");
            z3::ast::BV::bvnot(&bv).into()
        } else if function_name == "bvneg" {
            let bv = argument_values[0]
                .as_bv()
                .expect("bvneg arg must be bitvector");
            z3::ast::BV::bvneg(&bv).into()
        } else if function_name == "bvlshr" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvlshr arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvlshr arg 2 must be bitvector");
            z3::ast::BV::bvlshr(&bv1, &bv2).into()
        } else if function_name == "bvashr" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvashr arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvashr arg 2 must be bitvector");
            z3::ast::BV::bvashr(&bv1, &bv2).into()
        } else if function_name == "bvshl" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvshl arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvshl arg 2 must be bitvector");
            z3::ast::BV::bvshl(&bv1, &bv2).into()
        } else if function_name == "bvudiv" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvudiv arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvudiv arg 2 must be bitvector");
            z3::ast::BV::bvudiv(&bv1, &bv2).into()
        } else if function_name == "bvurem" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvurem arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvurem arg 2 must be bitvector");
            z3::ast::BV::bvurem(&bv1, &bv2).into()
        } else if function_name == "bvsdiv" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvsdiv arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvsdiv arg 2 must be bitvector");
            z3::ast::BV::bvsdiv(&bv1, &bv2).into()
        } else if function_name == "bvsrem" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvsrem arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvsrem arg 2 must be bitvector");
            z3::ast::BV::bvsrem(&bv1, &bv2).into()
        } else if function_name == "bvsmod" {
            let bv1 = argument_values[0]
                .as_bv()
                .expect("bvsmod arg 1 must be bitvector");
            let bv2 = argument_values[1]
                .as_bv()
                .expect("bvsmod arg 2 must be bitvector");
            z3::ast::BV::bvsmod(&bv1, &bv2).into()
        } else {
            todo!("Add Z3 function: ({function_name} {argument_values:?})");
        }
    }

    /// Handles indexed Z3 functions (functions with index parameters like extract, zero_extend, etc.)
    fn call_indexed_z3_function(
        &self,
        function_name: &str,
        indices: &[smt2parser::visitors::Index],
        argument_values: Vec<Dynamic>,
    ) -> Dynamic {
        if function_name == "extract" {
            if indices.len() != 2 {
                panic!("extract requires exactly 2 indices (high, low)");
            }
            let high = if let smt2parser::visitors::Index::Numeral(n) = &indices[0] {
                n.to_string()
                    .parse::<u32>()
                    .expect("extract high index must be u32")
            } else {
                panic!("extract high index must be a numeral");
            };
            let low = if let smt2parser::visitors::Index::Numeral(n) = &indices[1] {
                n.to_string()
                    .parse::<u32>()
                    .expect("extract low index must be u32")
            } else {
                panic!("extract low index must be a numeral");
            };
            if argument_values.len() != 1 {
                panic!("extract requires exactly 1 argument");
            }
            let bv = argument_values[0]
                .as_bv()
                .expect("extract argument must be a bitvector");
            z3::ast::BV::extract(&bv, high, low).into()
        } else if function_name == "zero_extend" {
            if indices.len() != 1 {
                panic!("zero_extend requires exactly 1 index");
            }
            let n = if let smt2parser::visitors::Index::Numeral(num) = &indices[0] {
                num.to_string()
                    .parse::<u32>()
                    .expect("zero_extend index must be u32")
            } else {
                panic!("zero_extend index must be a numeral");
            };
            if argument_values.len() != 1 {
                panic!("zero_extend requires exactly 1 argument");
            }
            let bv = argument_values[0]
                .as_bv()
                .expect("zero_extend argument must be a bitvector");
            z3::ast::BV::zero_ext(&bv, n).into()
        } else if function_name == "sign_extend" {
            if indices.len() != 1 {
                panic!("sign_extend requires exactly 1 index");
            }
            let n = if let smt2parser::visitors::Index::Numeral(num) = &indices[0] {
                num.to_string()
                    .parse::<u32>()
                    .expect("sign_extend index must be u32")
            } else {
                panic!("sign_extend index must be a numeral");
            };
            if argument_values.len() != 1 {
                panic!("sign_extend requires exactly 1 argument");
            }
            let bv = argument_values[0]
                .as_bv()
                .expect("sign_extend argument must be a bitvector");
            z3::ast::BV::sign_ext(&bv, n).into()
        } else {
            todo!(
                "Add indexed Z3 function: (_ {function_name} {:?}) with args {argument_values:?}",
                indices
            );
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
            .borrow_mut()
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
