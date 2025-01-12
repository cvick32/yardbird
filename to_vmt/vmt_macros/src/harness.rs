use proc_macro2::TokenStream;
use quote::{format_ident, quote};

pub fn translate_to_vmtil(fn_item: TokenStream) -> TokenStream {
    let syn::ItemFn {
        attrs,
        vis: _,
        sig,
        block,
    } = syn::parse2(fn_item).unwrap();

    let new_ident = format_ident!("__to_vmt_build_model_{}", sig.ident);

    let fn_arguments = sig.inputs.iter().filter_map(|arg| {
        if let syn::FnArg::Typed(syn::PatType { pat, ty: _, .. }) = arg {
            if let syn::Pat::Ident(pat_ident) = pat.as_ref() {
                if pat_ident.mutability.is_some() {
                    let ident_name = &pat_ident.ident.to_string();
                    return Some(quote! { .var_mut( #ident_name ) });
                } else {
                    let ident_name = &pat_ident.ident.to_string().to_uppercase();
                    return Some(quote! { .var_immut( #ident_name ) });
                }
            }
        }
        None
    });

    let parsed_block = parse_block(*block);

    quote! {
        #[allow(unused)]
        #(#attrs)* fn #new_ident () -> ::to_vmt::VMTModel {
            let mut builder = ::to_vmt::vmtil::VmtilBuilder::default();
            builder #(#fn_arguments)*;
            builder #parsed_block;

            builder.build_model()
        }
    }
}

fn parse_block(block: syn::Block) -> TokenStream {
    let stmts = block.stmts.into_iter().map(|st| {
        let stmt = parse_stmt(st);
        quote! { .stmt(#stmt) }
    });
    quote! {
        #(#stmts)*
    }
}

fn parse_stmt(stmt: syn::Stmt) -> vmtil::Stmt {
    match stmt {
        syn::Stmt::Local(_local) => todo!("local"),
        syn::Stmt::Item(_item) => todo!("item"),
        syn::Stmt::Expr(syn::Expr::Assign(syn::ExprAssign { left, right, .. }), _) => match *left {
            syn::Expr::Index(syn::ExprIndex { expr, index, .. }) => match (*expr, *index) {
                (syn::Expr::Path(expr_path), syn::Expr::Path(index_path)) => vmtil::Stmt::store(
                    path_string(&expr_path),
                    path_string(&index_path),
                    parse_expr(*right),
                ),
                _ => todo!("index"),
            },
            _ => todo!("index"),
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
                            lb,
                            path_string(ub),
                            vmtil::Stmt::Block {
                                stmts: body.stmts.into_iter().map(parse_stmt).collect(),
                            },
                        );
                    }
                }
            }
            todo!("Only support ranges for now: {expr:#?}")
        }
        syn::Stmt::Expr(expr, _semi) => todo!("unsupported expr stmt: {expr:#?}"),
        syn::Stmt::Macro(_stmt_macro) => todo!("macro"),
    }
}

// TODO: make this return an expr, I guess we should match the Rust grammar more
fn parse_expr(expr: syn::Expr) -> vmtil::Expr {
    match expr {
        syn::Expr::Index(syn::ExprIndex { expr, index, .. }) => match (*expr, *index) {
            (syn::Expr::Path(expr_path), syn::Expr::Path(index_path)) => {
                vmtil::Expr::select(path_string(&expr_path), path_string(&index_path))
            }
            _ => todo!("expr index"),
        },
        expr => todo!("unsupported expr: {expr:#?}"),
    }
}

fn path_string(path: &syn::ExprPath) -> String {
    path.path
        .segments
        .iter()
        .map(|ident| ident.ident.to_string())
        .collect::<Vec<_>>()
        .join(".")
}
