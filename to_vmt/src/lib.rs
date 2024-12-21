extern crate proc_macro;
use darling::ast::NestedMeta;
use darling::FromMeta;
use proc_macro::TokenStream;
use quote::quote_spanned;
use smt2parser::{concrete::Command, get_command_from_command_string, vmt::NEXT_VARIABLE_NAME};
use std::fmt::{Debug, Display};
use std::panic;
use std::time::Duration;
use syn::spanned::Spanned;
use syn::{Expr, ItemFn, Pat, PatIdent, PatType, Path};
use transition_system::to_vmt_model;

mod run_yardbird;
mod transition_system;

#[derive(Debug, FromMeta)]
struct ToVMTArgs {
    #[darling(default)]
    timeout: Option<u16>,
    prover: Option<String>,
    print_vmt: Option<bool>,
}

impl ToVMTArgs {
    fn from(attrs: TokenStream) -> Self {
        let attr_args = match NestedMeta::parse_meta_list(attrs.into()) {
            Ok(v) => v,
            Err(e) => {
                panic!("Error during attribute parsing: {e}");
            }
        };
        match ToVMTArgs::from_list(&attr_args) {
            Ok(v) => v,
            Err(e) => {
                panic!("Error building ToVMTArgs from_list(): {e}");
            }
        }
    }

    pub fn run_yardbird(&self) -> bool {
        self.prover
            .clone()
            .is_some_and(|prover| prover == "yardbird")
    }

    pub fn get_timeout(&self) -> Duration {
        if self.timeout.is_none() {
            Duration::from_secs(10)
        } else {
            Duration::from_secs(self.timeout.unwrap().into())
        }
    }
}

#[proc_macro_attribute]
pub fn to_vmt(attrs: TokenStream, item: TokenStream) -> TokenStream {
    let macro_args = ToVMTArgs::from(attrs);
    let content = to_vmt_inner(macro_args, proc_macro2::TokenStream::from(item));
    TokenStream::from(content)
}

#[derive(PartialEq, Eq)]
enum ParsingState {
    Precondition,
    Loop,
    Postcondition,
}

fn to_vmt_inner(macro_args: ToVMTArgs, item: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let pre_item = item.clone();
    let parsed: ItemFn = syn::parse(item.into()).unwrap();
    let function_name = parsed.sig.ident.to_string();
    let mut function_arguments = vec![];
    for input in parsed.sig.inputs {
        match input {
            syn::FnArg::Receiver(recv) => {
                return quote_spanned! {
                    recv.self_token.span() => compile_error!("Methods cannot be cast to VMT!");
                }
            }
            syn::FnArg::Typed(pat_type) => {
                let arg = FunctionArgument::from(pat_type);
                function_arguments.push(arg);
            }
        }
    }
    let (pre_condition_asserts, all_loop_asserts, post_condition_asserts) =
        build_transition_system(*parsed.block, &function_arguments);
    let vmt = to_vmt_model(
        function_arguments,
        pre_condition_asserts,
        all_loop_asserts,
        post_condition_asserts,
    );

    if macro_args.run_yardbird() {
        run_yardbird::run_yardbird(&macro_args, vmt.clone());
    }
    if macro_args
        .print_vmt
        .is_some_and(|should_print| should_print)
    {
        vmt.write_vmt_out(Some(format!("{function_name}.vmt")));
    }
    pre_item
}

fn build_transition_system(
    block: syn::Block,
    variables: &Vec<FunctionArgument>,
) -> (Vec<String>, Vec<Vec<String>>, Vec<String>) {
    let mut parsing_state = ParsingState::Precondition;
    let mut pre_condition_asserts = vec![];
    let mut all_loop_asserts: Vec<Vec<String>> = vec![];
    let mut post_condition_asserts = vec![];
    for stmt in block.stmts {
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
                                syn::Stmt::Expr(expr, _) => {
                                    match expr_to_smt2_string(expr, variables) {
                                        ExprReturn::String(smt2_string) => {
                                            loop_asserts.push(smt2_string)
                                        }
                                        ExprReturn::ArrayAccess(_) => todo!(),
                                    }
                                }
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
                let assert_string =
                    unwrap_assert_macro_to_smtlib2_expr_string(stmt_macro, variables);
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
    (
        pre_condition_asserts,
        all_loop_asserts,
        post_condition_asserts,
    )
}

fn unwrap_assert_macro_to_smtlib2_expr_string(
    stmt_macro: syn::StmtMacro,
    variables: &Vec<FunctionArgument>,
) -> String {
    if stmt_macro.mac.path.segments[0].ident != "assert" {
        todo!("Do not handle non-assert macros in to_vmt!");
    }
    let parsed_expr: Expr = syn::parse2(stmt_macro.mac.tokens).unwrap();
    match expr_to_smt2_string(parsed_expr, variables) {
        ExprReturn::String(smt2_string) => smt2_string,
        ExprReturn::ArrayAccess(_) => todo!(),
    }
}

#[derive(PartialEq, Eq)]
enum ExprReturn {
    String(String),
    ArrayAccess((String, String)),
}

fn expr_to_smt2_string(expr: Expr, variables: &Vec<FunctionArgument>) -> ExprReturn {
    match expr {
        Expr::Assign(expr_assign) => {
            let rhs = match expr_to_smt2_string(*expr_assign.right, variables) {
                ExprReturn::String(rhs_string) => rhs_string,
                ExprReturn::ArrayAccess((array, index)) => format!("(select {array} {index})"),
            };
            match expr_to_smt2_string(*expr_assign.left, variables) {
                ExprReturn::String(lhs_string) => {
                    ExprReturn::String(format!("(= {lhs_string}_{NEXT_VARIABLE_NAME} {rhs})"))
                }
                ExprReturn::ArrayAccess((array, index)) => ExprReturn::String(format!(
                    "(= {array}_{NEXT_VARIABLE_NAME} (store {array} {index} {rhs}))"
                )),
            }
        }
        Expr::Binary(expr_binary) => {
            let lhs = match expr_to_smt2_string(*expr_binary.left, variables) {
                ExprReturn::String(expr_str) => expr_str,
                ExprReturn::ArrayAccess((array, index)) => format!("(select {array} {index})"),
            };
            let rhs = match expr_to_smt2_string(*expr_binary.right, variables) {
                ExprReturn::String(expr_str) => expr_str,
                ExprReturn::ArrayAccess((array, index)) => format!("(select {array} {index})"),
            };
            match get_smt2_bin_op_string(expr_binary.op) {
                OpReturn::Single(op) => ExprReturn::String(format!("({op} {lhs} {rhs})")),
                OpReturn::Double((outer_op, inner_op)) => {
                    if outer_op.eq("=") {
                        // Really, this is an assignment so we have to update next.
                        ExprReturn::String(format!(
                            "({outer_op} {lhs}_{NEXT_VARIABLE_NAME} ({inner_op} {lhs} {rhs}))"
                        ))
                    } else {
                        ExprReturn::String(format!("({outer_op} ({inner_op} {lhs} {rhs}))"))
                    }
                }
            }
        }
        Expr::If(expr_if) => {
            let if_str = match expr_to_smt2_string(*expr_if.cond, variables) {
                ExprReturn::String(expr_str) => expr_str,
                _ => panic!("If condition cannot be an array expression!"),
            };
            let mut body = vec![];
            for stmt in expr_if.then_branch.stmts {
                match stmt {
                    syn::Stmt::Expr(expr, _) => {
                        let body_expr = match expr_to_smt2_string(expr, variables) {
                            ExprReturn::String(expr_string) => expr_string,
                            _ => panic!("Top-level body expression cannot be array expression."),
                        };
                        body.push(body_expr);
                    }
                    _ => panic!("Only expressions allowed in if body: {stmt:?}"),
                }
            }
            let body_string = body.join(" ");
            if expr_if.else_branch.is_none()
                || else_branch_only_contains_break(*expr_if.else_branch.unwrap().1)
            {
                let mut frames = vec![];
                for variable in variables {
                    if variable.is_mutable {
                        frames.push(variable.get_frame_expression());
                    }
                }
                let frame_str = frames.join(" ");
                ExprReturn::String(format!(
                    "(and (=> {if_str} (and {body_string})) (=> (not {if_str}) (and {frame_str})))"
                ))
            } else {
                todo!("Handle more complex expressions in else branch.")
            }
        }
        Expr::Index(expr_index) => {
            let array = match expr_to_smt2_string(*expr_index.expr, variables) {
                ExprReturn::String(array_string) => array_string,
                _ => panic!("Array call must be a single array.s"),
            };
            let index = match expr_to_smt2_string(*expr_index.index, variables) {
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
        Expr::Path(expr_path) => {
            let var_ident = expr_path.path.segments[0].ident.to_string();
            for variable in variables {
                if variable.is_equal(&var_ident) {
                    return ExprReturn::String(variable.vmt_name.clone());
                }
            }
            ExprReturn::String(var_ident)
        }
        _ => panic!("Cannot parse expression in asserts: {expr:?}"),
    }
}

fn else_branch_only_contains_break(else_branch: Expr) -> bool {
    match else_branch {
        Expr::Block(expr_block) => {
            expr_block.block.stmts.len() == 1
                && matches!(
                    expr_block.block.stmts[0],
                    syn::Stmt::Expr(Expr::Break(_), _)
                )
        }
        _ => panic!("Else branch must start with an Expr::Block!"),
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
        syn::BinOp::SubAssign(_) => OpReturn::Double(("=".into(), "-".into())),
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
        syn::BinOp::Gt(_) => OpReturn::Single(">".into()),
        syn::BinOp::Ge(_) => OpReturn::Single(">=".into()),
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
    pub rust_name: String,
    pub vmt_name: String,
    pub _pattern: PatIdent,
    pub is_mutable: bool,
    pub arg_type: ArgumentType,
}

impl FunctionArgument {
    pub fn from(pat_type: PatType) -> Self {
        let (rust_name, _pattern, is_mutable) = get_arg_innards(*pat_type.pat);
        let arg_type = ArgumentType::from(*pat_type.ty);
        // CONVENTION: when an argument is immutable, it is uppercased.
        let vmt_name = if is_mutable {
            rust_name.clone()
        } else {
            rust_name.to_uppercase()
        };
        FunctionArgument {
            rust_name,
            vmt_name,
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
        let cur_var = format!("(declare-fun {} () {})", self.vmt_name, arg_type);
        let next_var = format!(
            "(declare-fun {}_{} () {})",
            self.vmt_name, NEXT_VARIABLE_NAME, arg_type
        );
        let variable_relationship = format!(
            "(define-fun .{} () {} (! {} :next {}_{}))",
            self.vmt_name, arg_type, self.vmt_name, self.vmt_name, NEXT_VARIABLE_NAME
        );

        vec![
            get_command_from_command_string(cur_var.as_bytes()),
            get_command_from_command_string(next_var.as_bytes()),
            get_command_from_command_string(variable_relationship.as_bytes()),
        ]
    }

    fn is_equal(&self, str_value: &str) -> bool {
        self.rust_name.eq(str_value)
    }

    fn get_frame_expression(&self) -> String {
        format!(
            "(= {} {}_{NEXT_VARIABLE_NAME})",
            self.vmt_name, self.vmt_name
        )
    }
}

impl Display for FunctionArgument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_mutable {
            f.write_str("mut ")?;
        }
        f.write_str(&self.rust_name)?;
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
