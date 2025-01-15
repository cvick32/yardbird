use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{punctuated::Punctuated, Token};

#[derive(Debug)]
struct ArgStruct {
    fn_name: syn::Ident,
    #[allow(unused)]
    comma: Option<Token![,]>,
    keywords: Punctuated<Keyword, Token![,]>,
}

#[derive(Debug)]
struct Keyword {
    pub ident: syn::Ident,
    #[allow(unused)]
    pub equals: Token![=],
    pub expr: syn::Expr,
}

impl syn::parse::Parse for ArgStruct {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let fn_name = input.parse()?;
        let comma = input.parse().ok();
        let keywords = Punctuated::<Keyword, Token![,]>::parse_terminated(input).expect("b");
        Ok(ArgStruct {
            fn_name,
            comma,
            keywords,
        })
    }
}

impl syn::parse::Parse for Keyword {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Keyword {
            ident: input.parse()?,
            equals: input.parse()?,
            expr: input.parse()?,
        })
    }
}

pub fn check_to_depth(tokens: TokenStream) -> TokenStream {
    let args: ArgStruct = syn::parse2(tokens).unwrap();
    let test_name = format_ident!("test_{}", args.fn_name);
    let build_model_ident = format_ident!("__to_vmt_build_model_{}", args.fn_name);

    let run_model_args = args
        .keywords
        .into_iter()
        .map(|Keyword { ident, expr, .. }| {
            quote! {
                #ident: #expr
            }
        });

    quote! {
        #[allow(clippy::needless_update)]
        #[test]
        fn #test_name() {
            assert!(::to_vmt::run_model(::to_vmt::RunModelArgs {
                builder: #build_model_ident(),
                #(#run_model_args,)*
                ..Default::default()
            }))
        }
    }
}
