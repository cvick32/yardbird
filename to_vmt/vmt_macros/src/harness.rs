use proc_macro2::TokenStream;
use quote::{format_ident, quote};

pub fn translate_to_vmtil(ensures_clause: TokenStream, fn_item: TokenStream) -> TokenStream {
    let syn::ItemFn {
        attrs,
        vis: _,
        sig,
        block,
    } = syn::parse2(fn_item).unwrap();

    let new_ident = format_ident!("__to_vmt_build_model_{}", sig.ident);

    let fn_arguments = sig.inputs.iter().filter_map(|arg| {
        if let syn::FnArg::Typed(syn::PatType { pat, ty, .. }) = arg {
            if let syn::Pat::Ident(pat_ident) = pat.as_ref() {
                if pat_ident.mutability.is_some() {
                    let ident_name = &pat_ident.ident.to_string();
                    let type_name = parse_type(ty);
                    return Some(quote! { .var_mut( #ident_name, #type_name ) });
                } else {
                    let ident_name = &pat_ident.ident.to_string();
                    let type_name = parse_type(ty);
                    return Some(quote! { .var_immut( #ident_name, #type_name ) });
                }
            }
        }
        None
    });

    let parsed_ensures_clause = parse_ensures(ensures_clause);
    let parsed_block = parse_block(*block);

    quote! {
        #[allow(unused)]
        #(#attrs)* fn #new_ident () -> ::to_vmt::vmtil::VmtilBuilder {
            let mut builder = ::to_vmt::vmtil::VmtilBuilder::default();
            builder #(#fn_arguments)*;
            builder #parsed_ensures_clause;
            builder #parsed_block;

            builder
        }
    }
}

fn parse_ensures(clause: TokenStream) -> TokenStream {
    let syn::ExprClosure { inputs, body, .. } = syn::parse2(clause).unwrap();
    if let Some(syn::Pat::Ident(ident)) = inputs.first() {
        let body = parse_boolean_expr(*body);
        let forall = vmtil::BooleanExpr::forall(ident.ident.to_string(), body);
        quote! {
            .post_condition( #forall )
        }
    } else {
        todo!("Only support forall over a single variable")
    }
}

fn parse_block(block: syn::Block) -> TokenStream {
    let stmts = block.stmts.into_iter().map(|st| {
        if let syn::Stmt::Local(local) = st {
            parse_local(local)
        } else {
            let stmt = parse_stmt(st);
            quote! { .stmt(#stmt) }
        }
    });
    quote! {
        #(#stmts)*
    }
}

fn parse_type(ty: &syn::Type) -> vmtil::Type {
    match ty {
        syn::Type::Path(syn::TypePath { path, .. })
            if path.segments.len() == 1 && path.segments[0].ident == "Vec" =>
        {
            let segment = &path.segments[0];
            let arg_type = match &segment.arguments {
                syn::PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
                    args,
                    ..
                }) => match &args[0] {
                    syn::GenericArgument::Type(ty) => parse_type(ty),
                    _ => todo!("Parsing for generic arguments"),
                },
                _ => todo!("Parsing for segment arguments"),
            };
            vmtil::Type::Array {
                index: Box::new(vmtil::Type::Int),
                value: Box::new(arg_type),
            }
        }
        syn::Type::Path(syn::TypePath { path, .. }) => match path_string(path).as_str() {
            "usize" => vmtil::Type::Int,
            x => todo!("unsupported type: {x}"),
        },
        x => todo!("Type Parsing for {x:#?}"),
    }
}

// fn parse_type_ident(path: &syn::Path) -> vmtil::Type {}

fn parse_stmt(stmt: syn::Stmt) -> vmtil::Stmt {
    match stmt {
        syn::Stmt::Local(_) => todo!("local"),
        syn::Stmt::Item(_item) => todo!("item"),
        syn::Stmt::Expr(syn::Expr::Assign(syn::ExprAssign { left, right, .. }), _) => match *left {
            syn::Expr::Index(syn::ExprIndex { expr, index, .. }) => match (*expr, *index) {
                (syn::Expr::Path(expr_path), syn::Expr::Path(index_path)) => vmtil::Stmt::store(
                    path_string(&expr_path.path),
                    path_string(&index_path.path),
                    parse_expr(*right),
                ),
                _ => todo!("index"),
            },
            _ => todo!("index"),
        },
        syn::Stmt::Expr(
            syn::Expr::Binary(syn::ExprBinary {
                left, op, right, ..
            }),
            _,
        ) => match *left {
            syn::Expr::Path(syn::PatPath { path, .. }) => vmtil::Stmt::assign(
                path_string(&path),
                vmtil::Expr::arith_binop(
                    syn_binop_string(op),
                    path_string(&path),
                    parse_expr(*right),
                ),
            ),
            _ => todo!("hi"),
        },
        syn::Stmt::Expr(
            syn::Expr::ForLoop(syn::ExprForLoop {
                attrs: _,
                label: _,
                for_token: _,
                pat: _,
                in_token: _,
                expr,
                body,
            }),
            _,
        ) => {
            if let syn::Expr::Range(syn::ExprRange {
                attrs: _,
                mut start,
                limits: _,
                mut end,
            }) = *expr.clone()
            {
                if let (Some(syn::Expr::Lit(lb)), Some(syn::Expr::Path(ub))) =
                    (start.take().as_deref(), end.take().as_deref())
                {
                    if let syn::Lit::Int(lb) = &lb.lit {
                        return vmtil::Stmt::for_loop(
                            "i",
                            vmtil::Expr::Lit(lb.to_string()),
                            path_string(&ub.path),
                            vmtil::Stmt::Block {
                                stmts: body.stmts.into_iter().map(parse_stmt).collect(),
                            },
                        );
                    }
                }
            }
            todo!("Only support ranges for now: {expr:#?}")
        }
        syn::Stmt::Expr(syn::Expr::Loop(syn::ExprLoop { body, .. }), _) => {
            vmtil::Stmt::loop_stmt(vmtil::Stmt::Block {
                stmts: body.stmts.into_iter().map(parse_stmt).collect(),
            })
        }
        syn::Stmt::Expr(syn::Expr::Break(_), _) => vmtil::Stmt::Break,
        syn::Stmt::Expr(
            syn::Expr::If(syn::ExprIf {
                cond,
                then_branch,
                else_branch,
                ..
            }),
            _,
        ) => vmtil::Stmt::if_stmt(
            parse_boolean_expr(*cond),
            vmtil::Stmt::Block {
                stmts: then_branch.stmts.into_iter().map(parse_stmt).collect(),
            },
            else_branch.map(|(_, else_branch)| -> vmtil::Stmt {
                match *else_branch {
                    syn::Expr::Block(syn::ExprBlock { block, .. }) => vmtil::Stmt::Block {
                        stmts: block.stmts.into_iter().map(parse_stmt).collect(),
                    },
                    _ => todo!("unsupported else block"),
                }
            }),
        ),
        syn::Stmt::Expr(expr, _semi) => todo!("unsupported expr stmt: {expr:#?}"),
        syn::Stmt::Macro(_stmt_macro) => todo!("macro"),
    }
}

/// TODO: hack until we have proper multi statement support
fn parse_local(local: syn::Local) -> TokenStream {
    let syn::Local { pat, init, .. } = local;
    match (pat, init) {
        (syn::Pat::Type(syn::PatType { pat, ty, .. }), Some(syn::LocalInit { expr, .. })) => {
            match *pat {
                syn::Pat::Ident(syn::PatIdent { ident, .. }) => {
                    let var = ident.to_string();
                    let ty = parse_type(&ty);
                    let expr = parse_expr(*expr);
                    quote!(.local_binding(#var, #ty, #expr))
                }
                _ => todo!("local"),
            }
        }
        _ => todo!("unsupported local expression"),
    }
}

fn parse_expr(expr: syn::Expr) -> vmtil::Expr {
    match expr {
        syn::Expr::Index(syn::ExprIndex { expr, index, .. }) => match (*expr, *index) {
            (syn::Expr::Path(expr_path), syn::Expr::Path(index_path)) => {
                vmtil::Expr::select(path_string(&expr_path.path), path_string(&index_path.path))
            }
            _ => todo!("expr index"),
        },
        syn::Expr::Path(path) => vmtil::Expr::Var(path_string(&path.path)),
        syn::Expr::Lit(syn::PatLit { lit, .. }) => match lit {
            syn::Lit::Int(lit_int) => vmtil::Expr::Lit(lit_int.to_string()),
            x => todo!("unsupported literal: {x:#?}"),
        },
        syn::Expr::Binary(syn::ExprBinary {
            left, op, right, ..
        }) => vmtil::Expr::arith_binop(syn_binop_string(op), parse_expr(*left), parse_expr(*right)),
        expr => todo!("unsupported expr: {expr:#?}"),
    }
}

fn parse_boolean_expr(expr: syn::Expr) -> vmtil::BooleanExpr {
    match expr {
        syn::Expr::MethodCall(syn::ExprMethodCall {
            receiver,
            method,
            args,
            ..
        }) if method == "implies" => vmtil::BooleanExpr::binop(
            "=>",
            parse_boolean_expr(*receiver),
            vmtil::BooleanExpr::Conjunction(args.into_iter().map(parse_boolean_expr).collect()),
        ),
        syn::Expr::Paren(syn::ExprParen { expr, .. }) => parse_boolean_expr(*expr),
        syn::Expr::Binary(syn::ExprBinary {
            left, op, right, ..
        }) => {
            vmtil::BooleanExpr::binop(syn_binop_string(op), parse_expr(*left), parse_expr(*right))
        }
        expr => todo!("unsupported boolean expr: {expr:#?}"),
    }
}

fn syn_binop_string(binop: syn::BinOp) -> &'static str {
    match binop {
        syn::BinOp::Add(_) => "+",
        syn::BinOp::AddAssign(_) => "+",
        syn::BinOp::Sub(_) => "-",
        syn::BinOp::SubAssign(_) => "-",
        syn::BinOp::Mul(_) => "*",
        syn::BinOp::MulAssign(_) => "*",
        syn::BinOp::Div(_) => "/",
        syn::BinOp::DivAssign(_) => "/",
        syn::BinOp::Rem(_) => "&",
        syn::BinOp::RemAssign(_) => "&",
        syn::BinOp::Eq(_) => "=",
        syn::BinOp::Lt(_) => "<",
        syn::BinOp::Le(_) => "<=",
        syn::BinOp::Ne(_) => "!=",
        syn::BinOp::Ge(_) => ">=",
        syn::BinOp::Gt(_) => ">",
        syn::BinOp::And(_) => "and",
        x => todo!("binop: {x:#?}"),
    }
}

fn path_string(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|ident| ident.ident.to_string())
        .collect::<Vec<_>>()
        .join(".")
}
