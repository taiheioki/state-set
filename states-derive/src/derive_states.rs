use proc_macro2::TokenStream;
use proc_macro_crate::{crate_name, FoundCrate};
use quote::{format_ident, quote};
use syn::{parse_quote, Data, DeriveInput, Error, Fields, Index, Path, WhereClause};

struct Context<'a> {
    input: &'a DeriveInput,
    state_set: &'a Path,
}

pub(crate) fn derive_states_impl(input: &DeriveInput) -> TokenStream {
    let state_set = find_crate("state-set");
    let ctx = Context {
        input,
        state_set: &state_set,
    };

    let (impl_generics, ty_generics, _) = input.generics.split_for_impl();
    let ident = &input.ident;
    let where_clause = gen_where_clause(&ctx);

    let num_states = num_states(&ctx);
    let into_index_body = into_index_body(&ctx);

    quote! {
        #[automatically_derived]
        impl #impl_generics #state_set::States for #ident #ty_generics #where_clause {
            const NUM_STATES: u32 = #num_states;

            #[inline]
            fn into_index(self) -> u32 {
                #into_index_body
            }

            #[inline]
            unsafe fn from_index_unchecked(index: u32) -> Self {
                // #from_index_unchecked_body
                todo!()
            }
        }
    }
}

fn find_crate(orig_name: &str) -> Path {
    match crate_name(orig_name)
        .unwrap_or_else(|_| panic!("the package `{orig_name}` is absent in Cargo.toml"))
    {
        FoundCrate::Itself => parse_quote! { crate },
        FoundCrate::Name(name) => {
            let ident = format_ident!("{name}");
            parse_quote! { ::#ident }
        }
    }
}

fn gen_where_clause(ctx: &Context) -> Option<WhereClause> {
    ctx.input.generics.where_clause.clone()
}

fn num_states(ctx: &Context) -> TokenStream {
    match &ctx.input.data {
        Data::Enum(data_enum) => {
            let total_states: Vec<_> = data_enum
                .variants
                .iter()
                .map(|variant| num_states_from_fields(ctx, &variant.fields))
                .collect();
            quote! { #( #total_states+ )* 0 }
        }
        Data::Struct(data_struct) => num_states_from_fields(ctx, &data_struct.fields),
        Data::Union(_) => {
            Error::new_spanned(ctx.input, "union is not supperted").to_compile_error()
        }
    }
}

fn num_states_from_fields(ctx: &Context, fields: &Fields) -> TokenStream {
    let state_set = ctx.state_set;

    if matches!(fields, Fields::Unit) {
        return quote! { 1 };
    }

    let punctuated = match fields {
        Fields::Unnamed(fields) => &fields.unnamed,
        Fields::Named(fields) => &fields.named,
        Fields::Unit => unreachable!(),
    };

    let factors: Vec<_> = punctuated
        .iter()
        .map(|field| {
            let field_type = &field.ty;
            quote! { <#field_type as #state_set::States>::NUM_STATES }
        })
        .collect();

    quote! { #( #factors* )* 1 }
}

fn into_index_body(ctx: &Context) -> TokenStream {
    match &ctx.input.data {
        Data::Enum(data_enum) => {
            let mut base = quote! { 0 };

            let arms: Vec<_> = data_enum
                .variants
                .iter()
                .map(|variant: &syn::Variant| {
                    let variant_ident = &variant.ident;
                    let field_idents = gen_idents(&variant.fields, "x");

                    let lhs = match &variant.fields {
                        Fields::Named(_) => {
                            quote! { Self::#variant_ident { #(#field_idents,)* } }
                        }
                        Fields::Unnamed(_) => {
                            quote! { Self::#variant_ident(#(#field_idents,)* ) }
                        }
                        Fields::Unit => quote! { Self::#variant_ident  },
                    };

                    let remainder =
                        into_index_body_from_fields(ctx, &variant.fields, &field_idents);
                    let rhs = quote! { #base + #remainder };

                    let num_states = num_states_from_fields(ctx, &variant.fields);
                    base = quote! { #base + #num_states };

                    quote! { #lhs => #rhs }
                })
                .collect();

            quote! {
                match self {
                    #(#arms,)*
                }
            }
        }
        Data::Struct(data_struct) => {
            let field_idents: Vec<_> = gen_idents(&data_struct.fields, "")
                .iter()
                .map(|ident| quote! { self.#ident })
                .collect();
            into_index_body_from_fields(ctx, &data_struct.fields, &field_idents)
        }
        Data::Union(_) => {
            Error::new_spanned(ctx.input, "union is not supperted").to_compile_error()
        }
    }
}

fn gen_idents(fields: &Fields, unnamed_prefix: &str) -> Vec<TokenStream> {
    match fields {
        Fields::Named(fields) => fields
            .named
            .iter()
            .map(|field| {
                let ident = field.ident.as_ref().unwrap();
                quote! { #ident }
            })
            .collect(),
        Fields::Unnamed(fields) => (0..fields.unnamed.len())
            .map(|i| {
                if unnamed_prefix.is_empty() {
                    let index = Index::from(i);
                    quote! { #index }
                } else {
                    let ident = format_ident!("{unnamed_prefix}{i}");
                    quote! { #ident }
                }
            })
            .collect(),
        Fields::Unit => vec![],
    }
}

fn into_index_body_from_fields(
    ctx: &Context,
    fields: &Fields,
    idents: &[TokenStream],
) -> TokenStream {
    let state_set = ctx.state_set;

    if matches!(fields, Fields::Unit) {
        return quote! { 0 };
    }

    let punctuated = match fields {
        Fields::Unnamed(fields) => &fields.unnamed,
        Fields::Named(fields) => &fields.named,
        Fields::Unit => unreachable!(),
    };

    let mut base = quote! { 1 };

    let terms: Vec<_> = punctuated
        .iter()
        .zip(idents.iter())
        .rev()
        .map(|(field, ident)| {
            let field_type = &field.ty;
            let term = quote! { <#field_type as #state_set::States>::into_index(#ident) * #base };
            base = quote! { #base * <#field_type as #state_set::States>::NUM_STATES };
            term
        })
        .collect();

    quote! { #( #terms+ )* 0 }
}
