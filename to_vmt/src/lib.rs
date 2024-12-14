extern crate proc_macro;
use std::fmt::{Debug, Display};

use proc_macro::TokenStream;
use smt2parser::{concrete::Command, get_command_from_command_string, vmt::NEXT_VARIABLE_NAME};
use syn::{Expr, ItemFn, Pat, PatIdent, PatType, Path};

#[derive(PartialEq, Eq)]
enum ParsingState {
    Precondition,
    Loop,
    Postcondition,
}

#[proc_macro_attribute]
pub fn to_vmt(attrs: TokenStream, item: TokenStream) -> TokenStream {
    let dd = item.clone();
    let parsed: ItemFn = syn::parse(item).unwrap();

    let function_name = parsed.sig.ident.to_string();
    let mut function_arguments = vec![];
    for input in parsed.sig.inputs {
        match input {
            syn::FnArg::Receiver(_) => panic!("Methods cannot be cast to VMT!"),
            syn::FnArg::Typed(pat_type) => {
                let arg = FunctionArgument::from(pat_type);
                println!("{}", arg);
                arg.to_commands()
                    .iter()
                    .for_each(|command| println!("{}", command));
                function_arguments.push(arg);
            }
        }
    }
    let mut parsing_state = ParsingState::Precondition;
    let mut pre_condition_asserts = vec![];
    let mut all_loop_asserts: Vec<Vec<String>> = vec![];
    let mut post_condition_asserts = vec![];
    for stmt in parsed.block.stmts {
        match stmt {
            syn::Stmt::Expr(expr, _) => {
                match expr {
                    Expr::Loop(expr_loop) => {
                        if parsing_state == ParsingState::Precondition {
                            // Entering the loop
                            parsing_state = ParsingState::Loop;
                        }
                        let mut loop_asserts = vec![];
                        for stmt in expr_loop.body.stmts {
                            match stmt {
                                syn::Stmt::Expr(expr, _) => match expr_to_smt2_string(expr) {
                                    ExprReturn::String(smt2_string) => {
                                        println!("{smt2_string}");
                                        loop_asserts.push(smt2_string)
                                    }
                                    ExprReturn::ArrayAccess(_) => todo!(),
                                },
                                _ => todo!("Only handle expressions in loop body!"),
                            }
                        }
                        all_loop_asserts.push(loop_asserts);
                    }
                    _ => todo!("Only handle raw loops in to_vmt!"),
                }
            }
            syn::Stmt::Macro(stmt_macro) => {
                if parsing_state == ParsingState::Loop {
                    // Pop out of the loop
                    parsing_state = ParsingState::Postcondition;
                }
                println!("Parsing macro.");
                let assert_string = unwrap_assert_macro_to_smtlib2_expr_string(stmt_macro);
                println!("{assert_string}");
                if parsing_state == ParsingState::Precondition {
                    pre_condition_asserts.push(assert_string);
                } else if parsing_state == ParsingState::Postcondition {
                    post_condition_asserts.push(assert_string);
                } else {
                    panic!("Invalid parsing state.");
                }
            }
            _ => panic!("Only handle Expressions and Macros in to_vmt!"),
        }
    }

    let x = format!(
        r#"
        fn {}() {{
            println!("entering");
            println!("attr tokens: {{}}", {args});
            println!("input tokens: {{}}", {input});
            println!("exiting");
        }}
    "#,
        function_name,
        args = attrs.into_iter().count(),
        input = dd.into_iter().count(),
    );
    x.parse().expect("Generated invalid tokens")
}

fn unwrap_assert_macro_to_smtlib2_expr_string(stmt_macro: syn::StmtMacro) -> String {
    if stmt_macro.mac.path.segments[0].ident != "assert" {
        todo!("Do not handle non-assert macros in to_vmt!");
    }
    // TODO: it might be better to deal with the TokenStream directly here instead of parsing?
    // Parsing is nice because we have a bit more structure.
    let parsed_expr: Expr = syn::parse2(stmt_macro.mac.tokens).unwrap();
    match expr_to_smt2_string(parsed_expr) {
        ExprReturn::String(smt2_string) => smt2_string,
        ExprReturn::ArrayAccess(_) => todo!(),
    }
}

#[derive(PartialEq, Eq)]
enum ExprReturn {
    String(String),
    ArrayAccess((String, String)),
}

fn expr_to_smt2_string(expr: Expr) -> ExprReturn {
    match expr {
        Expr::Assign(expr_assign) => {
            let rhs = match expr_to_smt2_string(*expr_assign.right) {
                ExprReturn::String(rhs_string) => rhs_string,
                ExprReturn::ArrayAccess((array, index)) => format!("(select {array} {index})"),
            };
            match expr_to_smt2_string(*expr_assign.left) {
                ExprReturn::String(lhs_string) => {
                    ExprReturn::String(format!("(= {lhs_string}_{NEXT_VARIABLE_NAME} {rhs})"))
                }
                ExprReturn::ArrayAccess((array, index)) => ExprReturn::String(format!(
                    "(= {array}_{NEXT_VARIABLE_NAME} (store {array} {index} {rhs}))"
                )),
            }
        }
        Expr::Binary(expr_binary) => {
            let lhs = match expr_to_smt2_string(*expr_binary.left) {
                ExprReturn::String(expr_str) => expr_str,
                ExprReturn::ArrayAccess((array, index)) => format!("(select {array} {index})"),
            };
            let rhs = match expr_to_smt2_string(*expr_binary.right) {
                ExprReturn::String(expr_str) => expr_str,
                ExprReturn::ArrayAccess((array, index)) => format!("(select {array} {index})"),
            };
            match get_smt2_bin_op_string(expr_binary.op) {
                OpReturn::Single(op) => ExprReturn::String(format!("({op} {lhs} {rhs})")),
                OpReturn::Double((outer_op, inner_op)) => {
                    if outer_op.eq("=") {
                        // Really, this is an assignment so we have to update next.
                        ExprReturn::String(format!(
                            "({outer_op} ({inner_op} {lhs}_{NEXT_VARIABLE_NAME} {rhs}))"
                        ))
                    } else {
                        ExprReturn::String(format!("({outer_op} ({inner_op} {lhs} {rhs}))"))
                    }
                }
            }
        }
        Expr::If(expr_if) => {
            let if_str = match expr_to_smt2_string(*expr_if.cond) {
                ExprReturn::String(expr_str) => expr_str,
                _ => panic!("If condition cannot be an array expression!"),
            };
            let mut body = vec![];
            for stmt in expr_if.then_branch.stmts {
                match stmt {
                    syn::Stmt::Expr(expr, _) => {
                        let body_expr = match expr_to_smt2_string(expr) {
                            ExprReturn::String(expr_string) => expr_string,
                            _ => panic!("Top-level body expression cannot be array expression."),
                        };
                        body.push(body_expr);
                    }
                    _ => panic!("Only expressions allowed in if body: {stmt:?}"),
                }
            }
            let body_string = body.join(" ");
            ExprReturn::String(format!("(=> {if_str} (and {body_string}))"))
        }
        Expr::Index(expr_index) => {
            let array = match expr_to_smt2_string(*expr_index.expr) {
                ExprReturn::String(array_string) => array_string,
                _ => panic!("Array call must be a single array.s"),
            };
            let index = match expr_to_smt2_string(*expr_index.index) {
                ExprReturn::String(index_string) => index_string,
                _ => panic!("Do not handle nested array indexes."),
            };
            ExprReturn::ArrayAccess((array, index))
        }
        Expr::Lit(expr_lit) => match expr_lit.lit {
            syn::Lit::Str(lit_str) => ExprReturn::String(lit_str.value()),
            syn::Lit::Int(lit_int) => ExprReturn::String(lit_int.to_string()),
            syn::Lit::Bool(lit_bool) => {
                ExprReturn::String(smt2_bool_string_from_bool(lit_bool.value))
            }
            _ => todo!("Haven't implemented Rust literal: {expr_lit:?}"),
        },
        Expr::Path(expr_path) => ExprReturn::String(expr_path.path.segments[0].ident.to_string()),
        _ => panic!("Cannot parse expression in asserts: {expr:?}"),
    }
}

fn smt2_bool_string_from_bool(value: bool) -> String {
    match value {
        true => "True".into(),
        false => "False".into(),
    }
}

/// Apply either a Single or Double operation. For Double, the first string is the
/// last operation to apply, so: Double(("not", "=")) on operands a and b should
/// evaluate to: (not (= a b)).
enum OpReturn {
    Single(String),
    Double((String, String)),
}

fn get_smt2_bin_op_string(op: syn::BinOp) -> OpReturn {
    match op {
        syn::BinOp::AddAssign(_) => OpReturn::Double(("=".into(), "+".into())),
        syn::BinOp::Ne(_) => OpReturn::Double(("not".into(), "=".into())),
        syn::BinOp::Add(_) => OpReturn::Single("+".into()),
        syn::BinOp::Sub(_) => OpReturn::Single("-".into()),
        syn::BinOp::Mul(_) => OpReturn::Single("*".into()),
        syn::BinOp::Div(_) => OpReturn::Single("/".into()),
        syn::BinOp::And(_) => OpReturn::Single("and".into()),
        syn::BinOp::Or(_) => OpReturn::Single("or".into()),
        syn::BinOp::Eq(_) => OpReturn::Single("=".into()),
        syn::BinOp::Lt(_) => OpReturn::Single("<".into()),
        syn::BinOp::Le(_) => OpReturn::Single("<=".into()),
        syn::BinOp::Ge(_) => OpReturn::Single(">".into()),
        syn::BinOp::Gt(_) => OpReturn::Single(">=".into()),
        _ => todo!("Haven't implemented binary operation: {op:?}"),
    }
}

#[derive(Debug)]
struct ArgumentType {
    pub name: String,
    pub _path: Path,
    pub children: Vec<ArgumentType>,
}

#[derive(Debug)]
struct FunctionArgument {
    pub name: String,
    pub _pattern: PatIdent,
    pub is_mutable: bool,
    pub arg_type: ArgumentType,
}

impl FunctionArgument {
    pub fn from(pat_type: PatType) -> Self {
        let (name, _pattern, is_mutable) = get_arg_innards(*pat_type.pat);
        let arg_type = ArgumentType::from(*pat_type.ty);
        FunctionArgument {
            name,
            _pattern,
            is_mutable,
            arg_type,
        }
    }

    /*
    (declare-fun a () (Array Int Int))
    (declare-fun a_next () (Array Int Int))
    (define-fun .a () (Array Int Int) (! a :next a_next))
    */
    pub fn to_commands(&self) -> Vec<Command> {
        let arg_type = self.arg_type.to_smt2_sort_string();
        let cur_var = format!("(declare-fun {} () {})", self.name, arg_type);
        let next_var = format!(
            "(declare-fun {}_{} () {})",
            self.name, NEXT_VARIABLE_NAME, arg_type
        );
        let variable_relationship = format!(
            "(define-fun .{} () {} (! {} :next {}_{}))",
            self.name, arg_type, self.name, self.name, NEXT_VARIABLE_NAME
        );

        vec![
            get_command_from_command_string(cur_var.as_bytes()),
            get_command_from_command_string(next_var.as_bytes()),
            get_command_from_command_string(variable_relationship.as_bytes()),
        ]
    }
}

impl Display for FunctionArgument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_mutable {
            f.write_str("mut ")?;
        }
        f.write_str(&self.name)?;
        f.write_str(": ")?;
        f.write_str(format!("{}", self.arg_type).as_str())
    }
}

fn get_arg_innards(pat: Pat) -> (String, PatIdent, bool) {
    match pat {
        syn::Pat::Ident(pat_ident) => (
            pat_ident.ident.to_string(),
            pat_ident.clone(),
            pat_ident.mutability.is_some(),
        ),
        syn::Pat::Const(_) => todo!(),
        syn::Pat::Path(_) => todo!(),
        syn::Pat::Lit(_) => todo!(),
        syn::Pat::Macro(_) => todo!(),
        syn::Pat::Or(_) => todo!(),
        syn::Pat::Paren(_) => todo!(),
        syn::Pat::Range(_) => todo!(),
        syn::Pat::Reference(_) => todo!(),
        syn::Pat::Rest(_) => todo!(),
        syn::Pat::Slice(_) => todo!(),
        syn::Pat::Struct(_) => todo!(),
        syn::Pat::Tuple(_) => todo!(),
        syn::Pat::TupleStruct(_) => todo!(),
        syn::Pat::Type(_) => todo!(),
        syn::Pat::Verbatim(_) => todo!(),
        syn::Pat::Wild(_) => todo!(),
        _ => todo!(),
    }
}

impl ArgumentType {
    pub fn from(pat_type: syn::Type) -> Self {
        match pat_type {
            syn::Type::Array(_) => todo!(),
            syn::Type::BareFn(_) => todo!(),
            syn::Type::Group(_) => todo!(),
            syn::Type::ImplTrait(_) => todo!(),
            syn::Type::Infer(_) => todo!(),
            syn::Type::Macro(_) => todo!(),
            syn::Type::Never(_) => todo!(),
            syn::Type::Paren(_) => todo!(),
            syn::Type::Path(type_path) => {
                assert!(type_path.path.segments.len() == 1);
                if !type_path.path.segments[0].arguments.is_empty() {
                    let mut children = vec![];
                    match &type_path.path.segments[0].arguments {
                        syn::PathArguments::None => todo!(),
                        syn::PathArguments::AngleBracketed(angle_bracketed_generic_arguments) => {
                            for argument in &angle_bracketed_generic_arguments.args {
                                match argument {
                                    syn::GenericArgument::Lifetime(_) => todo!(),
                                    syn::GenericArgument::Type(ty) => {
                                        children.push(ArgumentType::from(ty.clone()))
                                    }
                                    syn::GenericArgument::Const(_) => todo!(),
                                    syn::GenericArgument::AssocType(_) => todo!(),
                                    syn::GenericArgument::AssocConst(_) => todo!(),
                                    syn::GenericArgument::Constraint(_) => todo!(),
                                    _ => todo!(),
                                }
                            }
                            ArgumentType {
                                name: type_path.path.segments[0].ident.to_string(),
                                _path: type_path.path,
                                children,
                            }
                        }
                        syn::PathArguments::Parenthesized(_) => todo!(),
                    }
                } else {
                    ArgumentType {
                        name: type_path.path.segments[0].ident.to_string(),
                        _path: type_path.path,
                        children: vec![],
                    }
                }
            }
            syn::Type::Ptr(_) => todo!(),
            syn::Type::Reference(_) => todo!(),
            syn::Type::Slice(_) => todo!(),
            syn::Type::TraitObject(_) => todo!(),
            syn::Type::Tuple(_) => todo!(),
            syn::Type::Verbatim(_) => todo!(),
            _ => todo!(),
        }
    }

    /// TODO: Will Rust Vecs always be indexed by Int?
    /// This is a current limitation.
    fn to_smt2_sort_string(&self) -> String {
        if self.name == "Vec" {
            let args = self
                .children
                .iter()
                .map(|child| child.to_smt2_sort_string())
                .collect::<Vec<_>>()
                .join(" ");
            format!("(Array Int {args})")
        } else if self.name == "usize" {
            "Int".into()
        } else {
            todo!("Have not implemented SMT2 version of: {}", self.name)
        }
    }
}

impl Display for ArgumentType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)?;

        let child_string = if !self.children.is_empty() {
            let children = self
                .children
                .iter()
                .map(|arg| format!("{arg}"))
                .collect::<Vec<_>>()
                .join(" ");

            format!("<{children}>")
        } else {
            String::new()
        };
        f.write_str(&child_string)
    }
}
