use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{
    parse_quote, Data, DeriveInput, Error, Fields, GenericParam, Index, Path, TypeParam, Variant,
    WhereClause, WherePredicate,
};

struct Context<'a> {
    input: &'a DeriveInput,
    crate_path: &'a Path,
}

pub(crate) fn derive_state_impl(input: &DeriveInput) -> TokenStream {
    if matches!(input.data, Data::Union(_)) {
        return Error::new_spanned(input, "union is not supperted").to_compile_error();
    }

    let crate_path = parse_quote! { ::state_set };
    let ctx = Context {
        input,
        crate_path: &crate_path,
    };

    let (impl_generics, ty_generics, _) = input.generics.split_for_impl();
    let ident = &input.ident;
    let where_clause = gen_where_clause(&ctx);

    let num_states = gen_num_states(&ctx);
    let into_index = gen_into_index(&ctx);
    let from_index_unchecked = gen_from_index_unchecked(&ctx);

    quote! {
        #[automatically_derived]
        impl #impl_generics #crate_path::State for #ident #ty_generics #where_clause {
            #num_states
            #into_index
            #from_index_unchecked
        }
    }
}

fn gen_where_clause(ctx: &Context<'_>) -> Option<WhereClause> {
    let mut where_clause = ctx.input.generics.where_clause.clone();
    let crate_path = ctx.crate_path;

    for param in &ctx.input.generics.params {
        if let GenericParam::Type(TypeParam { ident, .. }) = param {
            let predicate: WherePredicate = parse_quote! { #ident: #crate_path::State };
            if let Some(WhereClause { predicates, .. }) = where_clause.as_mut() {
                predicates.push(predicate);
            } else {
                where_clause = Some(parse_quote! { where #predicate });
            }
        }
    }

    where_clause
}

/// Generate `State::NUM_STATES`.
fn gen_num_states(ctx: &Context<'_>) -> TokenStream {
    let rhs = match &ctx.input.data {
        Data::Enum(data_enum) => {
            let total_states = data_enum
                .variants
                .iter()
                .map(|variant| num_states_for_fields(ctx, &variant.fields));
            quote! { #( #total_states+ )* 0 }
        }
        Data::Struct(data_struct) => num_states_for_fields(ctx, &data_struct.fields),
        Data::Union(_) => unreachable!(),
    };

    quote! { const NUM_STATES: u32 = #rhs; }
}

fn num_states_for_fields(ctx: &Context<'_>, fields: &Fields) -> TokenStream {
    let crate_path = ctx.crate_path;

    if matches!(fields, Fields::Unit) {
        return quote! { 1 };
    }

    let punctuated = match fields {
        Fields::Unnamed(fields) => &fields.unnamed,
        Fields::Named(fields) => &fields.named,
        Fields::Unit => unreachable!(),
    };

    let factors = punctuated.iter().map(|field| {
        let field_type = &field.ty;
        quote! { <#field_type as #crate_path::State>::NUM_STATES }
    });

    quote! { #( #factors* )* 1 }
}

/// Generate `State::into_index`.
fn gen_into_index(ctx: &Context<'_>) -> TokenStream {
    let body = match &ctx.input.data {
        Data::Enum(data_enum) => {
            let mut base = quote! { 0 };

            let arms = data_enum.variants.iter().map(|variant: &Variant| {
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
                    gen_into_index_body_from_fields(ctx, &variant.fields, &field_idents);
                let rhs = quote! { #base + #remainder };

                let num_states = num_states_for_fields(ctx, &variant.fields);
                base = quote! { #base + #num_states };

                quote! { #lhs => #rhs }
            });

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
            gen_into_index_body_from_fields(ctx, &data_struct.fields, &field_idents)
        }
        Data::Union(_) => {
            Error::new_spanned(ctx.input, "union is not supperted").to_compile_error()
        }
    };

    quote! {
        #[inline]
        fn into_index(self) -> u32 {
            #body
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

fn gen_into_index_body_from_fields(
    ctx: &Context<'_>,
    fields: &Fields,
    idents: &[TokenStream],
) -> TokenStream {
    let crate_path = ctx.crate_path;

    if matches!(fields, Fields::Unit) {
        return quote! { 0 };
    }

    let punctuated = match fields {
        Fields::Unnamed(fields) => &fields.unnamed,
        Fields::Named(fields) => &fields.named,
        Fields::Unit => unreachable!(),
    };

    let mut base = quote! { 1 };

    let terms = punctuated.iter().zip(idents).rev().map(|(field, ident)| {
        let field_type = &field.ty;
        let term = quote! { <#field_type as #crate_path::State>::into_index(#ident) * #base };
        base = quote! { #base * <#field_type as #crate_path::State>::NUM_STATES };
        term
    });

    quote! { #( #terms+ )* 0 }
}

/// Generate `State::from_index_unchecked`.
fn gen_from_index_unchecked(ctx: &Context<'_>) -> TokenStream {
    let body = match &ctx.input.data {
        Data::Enum(data_enum) => {
            let mut iter = data_enum.variants.iter();
            if let Some(last_variant) = iter.next_back() {
                let statements = iter.map(|variant| {
                    let variant_ident = &variant.ident;
                    let num_states = num_states_for_fields(ctx, &variant.fields);
                    let init_list = fields_init_list(ctx, &variant.fields);

                    quote! {
                        if index < #num_states {
                            return Self::#variant_ident #init_list;
                        }
                        let index = index - #num_states;
                    }
                });

                let last_variant_ident = &last_variant.ident;
                let last_init_list = fields_init_list(ctx, &last_variant.fields);

                quote! {
                    #(#statements)*
                    Self::#last_variant_ident #last_init_list
                }
            } else {
                quote! { unreachable!() }
            }
        }
        Data::Struct(data_struct) => {
            let init_list = fields_init_list(ctx, &data_struct.fields);
            quote! { Self #init_list }
        }
        Data::Union(_) => unreachable!(),
    };

    quote! {
        #[allow(clippy::modulo_one)]
        #[inline]
        unsafe fn from_index_unchecked(index: u32) -> Self {
            #body
        }
    }
}

fn fields_init_list(ctx: &Context<'_>, fields: &Fields) -> TokenStream {
    let crate_path = ctx.crate_path;
    let mut base = quote! { 1 };

    match fields {
        Fields::Named(fields) => {
            let mut fields: Vec<_> = fields.named.iter().rev().map(|field| {
                let field_ident = field.ident.as_ref().unwrap();
                let field_type = &field.ty;
                let num_states = quote! { <#field_type as #crate_path::State>::NUM_STATES };
                let result = quote! {
                    #field_ident: <#field_type as #crate_path::State>::from_index_unchecked((index / (#base)) % #num_states)
                };
                base = quote! { #base * #num_states };
                result
            }).collect();
            fields.reverse();
            quote! { { #(#fields),* } }
        }
        Fields::Unnamed(fields) => {
            let mut fields: Vec<_> = fields.unnamed.iter().rev().map(|field| {
                let field_type = &field.ty;
                let num_states = quote! { <#field_type as #crate_path::State>::NUM_STATES };
                let result = quote! {
                    <#field_type as #crate_path::State>::from_index_unchecked((index / (#base)) % #num_states)
                };
                base = quote! { #base * #num_states };
                result
            }).collect();
            fields.reverse();
            quote! { (#(#fields),*) }
        }
        Fields::Unit => quote! {},
    }
}
