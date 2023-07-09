use proc_macro2::TokenStream;
use proc_macro_crate::{crate_name, FoundCrate};
use quote::{format_ident, quote};
use syn::{parse_quote, Data, DeriveInput, Error, Fields, Index, Path, WhereClause};

struct Context<'a> {
    input: &'a DeriveInput,
    state_set: &'a Path,
}

pub(crate) fn derive_state_impl(input: &DeriveInput) -> TokenStream {
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
    let from_index_unchecked_body = from_index_unchecked_body(&ctx);

    quote! {
        #[automatically_derived]
        impl #impl_generics #state_set::State for #ident #ty_generics #where_clause {
            const NUM_STATES: u32 = #num_states;

            #[inline]
            fn into_index(self) -> u32 {
                #into_index_body
            }

            #[inline]
            #[allow(clippy::modulo_one)]
            unsafe fn from_index_unchecked(index: u32) -> Self {
                #from_index_unchecked_body
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

/// Generates the value of `NUM_STATES`.
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
            quote! { <#field_type as #state_set::State>::NUM_STATES }
        })
        .collect();

    quote! { #( #factors* )* 1 }
}

/// Generates the body of `into_index`.
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
            let term = quote! { <#field_type as #state_set::State>::into_index(#ident) * #base };
            base = quote! { #base * <#field_type as #state_set::State>::NUM_STATES };
            term
        })
        .collect();

    quote! { #( #terms+ )* 0 }
}

/// Generate the body of `from_index_unchecked`.
fn from_index_unchecked_body(ctx: &Context) -> TokenStream {
    match &ctx.input.data {
        Data::Enum(data_enum) => {
            let statements: Vec<_> = data_enum
                .variants
                .iter()
                .map(|variant| {
                    let variant_ident = &variant.ident;
                    let num_states = num_states_from_fields(ctx, &variant.fields);
                    let fields_init = fields_init_list(ctx, &variant.fields);
                    quote! {
                        if index < #num_states {
                            return Self::#variant_ident #fields_init;
                        }
                        let index = index - #num_states;
                    }
                })
                .collect();

            quote! {
                #(#statements)*
                unreachable!()
            }
        }
        Data::Struct(data_struct) => {
            let fields_init = fields_init_list(ctx, &data_struct.fields);
            quote! { Self #fields_init }
        }
        Data::Union(_) => {
            Error::new_spanned(ctx.input, "union is not supported").to_compile_error()
        }
    }
}

fn fields_init_list(ctx: &Context, fields: &Fields) -> TokenStream {
    let state_set = ctx.state_set;
    let mut base = quote! { 1 };

    match fields {
        Fields::Named(fields) => {
            let mut fields: Vec<_> = fields.named.iter().rev().map(|field| {
                let field_ident = field.ident.as_ref().unwrap();
                let field_type = &field.ty;
                let num_states = quote! { <#field_type as #state_set::State>::NUM_STATES };
                let result = quote! { #field_ident: <#field_type as #state_set::State>::from_index_unchecked((index / (#base)) % #num_states) };
                base = quote! { #base * #num_states };
                result
            }).collect();
            fields.reverse();
            quote! { { #(#fields),* } }
        }
        Fields::Unnamed(fields) => {
            let mut fields: Vec<_> = fields.unnamed.iter().rev().map(|field| {
                let field_type = &field.ty;
                let num_states = quote! { <#field_type as #state_set::State>::NUM_STATES };
                let result = quote! { <#field_type as #state_set::State>::from_index_unchecked((index / (#base)) % #num_states) };
                base = quote! { #base * #num_states };
                result
            }).collect();
            fields.reverse();
            quote! { (#(#fields),*) }
        }
        Fields::Unit => quote! {},
    }
}
