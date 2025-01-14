use harness::translate_to_vmtil;
use proc_macro::TokenStream;
use quote::quote;

mod harness;
mod verify;

#[proc_macro_attribute]
pub fn ensures(attrs: TokenStream, item: TokenStream) -> TokenStream {
    let item = proc_macro2::TokenStream::from(item);
    let model_generator = translate_to_vmtil(attrs.into(), item.clone());
    let doubled = quote! {
        #item
        #model_generator
    };
    TokenStream::from(doubled)
}

#[proc_macro]
pub fn generate_test(item: TokenStream) -> TokenStream {
    verify::check_to_depth(item.into()).into()
}
