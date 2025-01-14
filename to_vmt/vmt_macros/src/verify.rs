use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Token;

#[derive(Debug)]
struct ArgStruct {
    depth: syn::Lit,
    #[allow(unused)]
    comma: Token![,],
    fn_name: syn::Ident,
}

impl syn::parse::Parse for ArgStruct {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(ArgStruct {
            depth: input.parse()?,
            comma: input.parse()?,
            fn_name: input.parse()?,
        })
    }
}

pub fn check_to_depth(tokens: TokenStream) -> TokenStream {
    let args: ArgStruct = syn::parse2(tokens).unwrap();
    // panic!("{args:#?}")
    let depth = args.depth;
    let build_model_ident = format_ident!("__to_vmt_build_model_{}", args.fn_name);
    quote! {
        ::to_vmt::run_model(#depth, #build_model_ident());
    }
}
