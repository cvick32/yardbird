extern crate proc_macro;
use std::fmt::{Debug, Display};

use proc_macro::TokenStream;
use smt2parser::{concrete::Command, get_command_from_command_string, vmt::NEXT_VARIABLE_NAME};
use syn::{Expr, ItemFn, Pat, PatIdent, PatType, Path};

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
    let mut assert_strings = vec![];
    for stmt in parsed.block.stmts {
        println!("{stmt:#?}");
        match stmt {
            syn::Stmt::Local(_) => todo!(),
            syn::Stmt::Item(_) => todo!(),
            syn::Stmt::Expr(expr, semi) => todo!(),
            syn::Stmt::Macro(stmt_macro) => {
                println!("Parsing macro.");
                let assert_string = unwrap_assert_macro_to_smtlib2_expr_string(stmt_macro);
                println!("{assert_string}");
                assert_strings.push(assert_string);
            }
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
    expr_to_smt2_string(parsed_expr)
}

fn expr_to_smt2_string(expr: Expr) -> String {
    match expr {
        Expr::Binary(expr_binary) => {
            let op = get_smt2_bin_op_string(expr_binary.op);
            let lhs = expr_to_smt2_string(*expr_binary.left);
            let rhs = expr_to_smt2_string(*expr_binary.right);
            format!("({op} {lhs} {rhs})")
        }
        Expr::Path(expr_path) => expr_path.path.segments[0].ident.to_string(),
        Expr::Lit(expr_lit) => match expr_lit.lit {
            syn::Lit::Str(lit_str) => lit_str.value(),
            syn::Lit::ByteStr(_) => todo!(),
            syn::Lit::CStr(_) => todo!(),
            syn::Lit::Byte(_) => todo!(),
            syn::Lit::Char(_) => todo!(),
            syn::Lit::Int(lit_int) => lit_int.to_string(),
            syn::Lit::Float(_) => todo!(),
            syn::Lit::Bool(lit_bool) => smt2_bool_string_from_bool(lit_bool.value),
            syn::Lit::Verbatim(_) => todo!(),
            _ => todo!(),
        },
        _ => panic!("Cannot parse non-binary expressions in asserts: {expr:?}"),
    }
}

fn smt2_bool_string_from_bool(value: bool) -> String {
    match value {
        true => "True".into(),
        false => "False".into(),
    }
}

fn get_smt2_bin_op_string(op: syn::BinOp) -> String {
    match op {
        syn::BinOp::Add(_) => "+".into(),
        syn::BinOp::Sub(_) => "-".into(),
        syn::BinOp::Mul(_) => "*".into(),
        syn::BinOp::Div(_) => "/".into(),
        syn::BinOp::And(_) => "and".into(),
        syn::BinOp::Or(_) => "or".into(),
        syn::BinOp::Eq(_) => "=".into(),
        syn::BinOp::Lt(_) => "<".into(),
        syn::BinOp::Le(_) => "<=".into(),
        syn::BinOp::Ge(_) => ">".into(),
        syn::BinOp::Gt(_) => ">=".into(),
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
