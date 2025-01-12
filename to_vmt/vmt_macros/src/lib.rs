use harness::translate_to_vmtil;
use proc_macro::TokenStream;
use quote::quote;

mod harness;

#[proc_macro_attribute]
pub fn to_vmt2(_attrs: TokenStream, item: TokenStream) -> TokenStream {
    let item = proc_macro2::TokenStream::from(item);
    let model_generator = translate_to_vmtil(item.clone());
    let doubled = quote! {
        #item
        #model_generator
    };
    TokenStream::from(doubled)
}
