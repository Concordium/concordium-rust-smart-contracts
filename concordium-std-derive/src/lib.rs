// #![no_std]
extern crate proc_macro;
extern crate syn;
#[macro_use]
extern crate quote;

use concordium_contracts_common::{ContractName, ReceiveName};
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::ToTokens;
#[cfg(feature = "build-schema")]
use std::collections::HashMap;
use std::{
    collections::{BTreeMap, BTreeSet},
    convert::TryFrom,
    ops::Neg,
};
use syn::{
    parse::Parser, parse_macro_input, punctuated::*, spanned::Spanned, DataEnum, Ident, Meta, Token,
};

/// A helper to report meaningful compilation errors
/// - If applied to an Ok value they simply return the underlying value.
/// - If applied to `Err(e)` then `e` is turned into a compiler error.
fn unwrap_or_report(v: syn::Result<TokenStream>) -> TokenStream {
    match v {
        Ok(ts) => ts,
        Err(e) => e.to_compile_error().into(),
    }
}

fn attach_error<A>(mut v: syn::Result<A>, msg: &str) -> syn::Result<A> {
    if let Err(e) = v.as_mut() {
        let span = e.span();
        e.combine(syn::Error::new(span, msg));
    }
    v
}

/// Attributes that can be attached either to the init or receive method of a
/// smart contract.
struct OptionalArguments {
    /// If set, the contract can receive CCD.
    pub(crate) payable:           bool,
    /// If enabled, the function has access to logging facilities.
    pub(crate) enable_logger:     bool,
    /// The function is a low-level one, with direct access to contract memory.
    pub(crate) low_level:         bool,
    /// Which type, if any, is the parameter type of the function.
    /// This is used when generating schemas.
    pub(crate) parameter:         Option<syn::LitStr>,
    /// Which type, if any, is the return value of the function.
    /// This is used when generating schemas.
    pub(crate) return_value:      Option<syn::LitStr>,
    /// Which type, if any, is the error type of the function.
    /// This is used when generating schemas.
    pub(crate) error:             Option<syn::LitStr>,
    /// If enabled, the function has access to cryptographic primitives.
    pub(crate) crypto_primitives: bool,
}

/// Attributes that can be attached to the initialization method.
struct InitAttributes {
    /// Name of the contract.
    pub(crate) contract: syn::LitStr,
    pub(crate) optional: OptionalArguments,
}

/// Attributes that can be attached to the receive method.
struct ReceiveAttributes {
    /// Name of the contract the method applies to.
    pub(crate) contract: syn::LitStr,
    /// Name of the method.
    pub(crate) name:     syn::LitStr,
    pub(crate) optional: OptionalArguments,
    /// If enabled, the function has access to a mutable state, which will also
    /// be stored after the function returns.
    pub(crate) mutable:  bool,
}

#[derive(Default)]
struct ParsedAttributes {
    /// We use BTreeSet to have consistent order of iteration when reporting
    /// errors.
    pub(crate) flags:  BTreeSet<syn::Ident>,
    /// We use BTreeMap to have consistent order of iteration when reporting
    /// errors.
    pub(crate) values: BTreeMap<syn::Ident, syn::LitStr>,
}

impl ParsedAttributes {
    /// Remove an attribute and return its value (i.e., right hand side of ident
    /// = value), if present. The key must be a valid Rust identifier,
    /// otherwise this function will panic.
    pub(crate) fn extract_value(&mut self, key: &str) -> Option<syn::LitStr> {
        self.extract_ident_and_value(key).map(|x| x.1)
    }

    /// Remove an attribute identifier and the value and return it, if present.
    /// The key must be a valid Rust identifier, otherwise this function
    /// will panic.
    pub(crate) fn extract_ident_and_value(
        &mut self,
        key: &str,
    ) -> Option<(syn::Ident, syn::LitStr)> {
        // This is not clean, constructing a new identifier with a call_site span.
        // But the only alternative I see is iterating over the map and locating the key
        // since Ident implements equality comparison with &str.
        let key = syn::Ident::new(key, Span::call_site());
        self.values.remove_entry(&key)
    }

    /// Remove an attribute and return whether it was present.
    pub(crate) fn extract_flag(&mut self, key: &str) -> Option<Ident> {
        // This is not clean, constructing a new identifier with a call_site span.
        // But the only alternative I see is iterating over the map and locating the key
        // since Ident implements equality comparison with &str.
        let key = syn::Ident::new(key, Span::call_site());
        self.flags.take(&key)
    }

    /// If there are any remaining attributes signal an error. Otherwise return
    /// Ok(())
    pub(crate) fn report_all_attributes(self) -> syn::Result<()> {
        // TODO: Replace into_iter + map with into_keys when only supporting rust 1.54+
        let mut iter = self.flags.into_iter().chain(self.values.into_iter().map(|(k, _)| k));
        if let Some(ident) = iter.next() {
            let mut err =
                syn::Error::new(ident.span(), format!("Unrecognized attribute {}.", ident));
            for next_ident in iter {
                err.combine(syn::Error::new(
                    ident.span(),
                    format!("Unrecognized attribute {}.", next_ident),
                ));
            }
            Err(err)
        } else {
            Ok(())
        }
    }
}

/// Parse attributes ensuring there are no duplicate items.
fn parse_attributes<'a>(iter: impl IntoIterator<Item = &'a Meta>) -> syn::Result<ParsedAttributes> {
    let mut ret = ParsedAttributes::default();
    let mut errors = Vec::new();
    let mut duplicate_values = BTreeMap::new();
    let mut duplicate_flags = BTreeMap::new();
    for attr in iter.into_iter() {
        match attr {
            Meta::NameValue(mnv) => {
                if let Some(ident) = mnv.path.get_ident() {
                    if let syn::Lit::Str(ls) = &mnv.lit {
                        if let Some((existing_ident, _)) = ret.values.get_key_value(ident) {
                            let v = duplicate_values.entry(ident).or_insert_with(|| {
                                syn::Error::new(
                                    existing_ident.span(),
                                    format!("Duplicate attribute '{}'.", existing_ident),
                                )
                            });
                            v.combine(syn::Error::new(
                                ident.span(),
                                format!("'{}' also appears here.", ident),
                            ));
                        } else {
                            ret.values.insert(ident.clone(), ls.clone());
                        }
                    } else {
                        errors.push(syn::Error::new(
                            mnv.path.span(),
                            format!(
                                "Values of attribute must be string literals, e.g., '{} = \
                                 \"value\"'",
                                ident
                            ),
                        ));
                    }
                } else {
                    errors.push(syn::Error::new(
                        mnv.path.span(),
                        "Unrecognized attribute. Only attribute names consisting of a single \
                         identifier are recognized.",
                    ))
                }
            }
            Meta::Path(p) => {
                if let Some(ident) = p.get_ident() {
                    if let Some(existing_ident) = ret.flags.get(ident) {
                        let v = duplicate_flags.entry(ident).or_insert_with(|| {
                            syn::Error::new(
                                existing_ident.span(),
                                format!("Duplicate attribute '{}'.", existing_ident),
                            )
                        });
                        v.combine(syn::Error::new(
                            ident.span(),
                            format!("'{}' also appears here.", ident),
                        ));
                    } else {
                        ret.flags.insert(ident.clone());
                    }
                } else {
                    errors.push(syn::Error::new(
                        p.span(),
                        "Unrecognized attribute. Only attribute names consisting of a single \
                         identifier are recognized.",
                    ))
                }
            }
            Meta::List(p) => {
                errors.push(syn::Error::new(p.span(), "Unrecognized attribute."));
            }
        }
    }
    // TODO: Replace with into_values when least rust version becomes 1.54.
    let mut iter = errors
        .into_iter()
        .chain(duplicate_values.into_iter().map(|(_, v)| v))
        .chain(duplicate_flags.into_iter().map(|(_, v)| v));
    // If there are any errors we combine them.
    if let Some(err) = iter.next() {
        let mut err = err;
        for next_err in iter {
            err.combine(next_err);
        }
        Err(err)
    } else {
        Ok(ret)
    }
}

// Supported attributes for the init methods.

const INIT_ATTRIBUTE_PARAMETER: &str = "parameter";
const INIT_ATTRIBUTE_CONTRACT: &str = "contract";
const INIT_ATTRIBUTE_PAYABLE: &str = "payable";
const INIT_ATTRIBUTE_ENABLE_LOGGER: &str = "enable_logger";
const INIT_ATTRIBUTE_LOW_LEVEL: &str = "low_level";
const INIT_ATTRIBUTE_RETURN_VALUE: &str = "return_value";
const INIT_ATTRIBUTE_ERROR: &str = "error";
const INIT_ATTRIBUTE_CRYPTO_PRIMITIVES: &str = "crypto_primitives";

fn parse_init_attributes<'a, I: IntoIterator<Item = &'a Meta>>(
    attrs: I,
) -> syn::Result<InitAttributes> {
    let mut attributes = parse_attributes(attrs)?;
    let contract: syn::LitStr =
        attributes.extract_value(INIT_ATTRIBUTE_CONTRACT).ok_or_else(|| {
            syn::Error::new(
                Span::call_site(),
                "A name for the contract must be provided, using the 'contract' attribute.\n\nFor \
                 example, #[init(contract = \"my-contract\")]",
            )
        })?;
    let parameter: Option<syn::LitStr> = attributes.extract_value(INIT_ATTRIBUTE_PARAMETER);
    let payable = attributes.extract_flag(INIT_ATTRIBUTE_PAYABLE).is_some();
    let enable_logger = attributes.extract_flag(INIT_ATTRIBUTE_ENABLE_LOGGER).is_some();
    let low_level = attributes.extract_flag(INIT_ATTRIBUTE_LOW_LEVEL).is_some();
    let return_value = attributes.extract_ident_and_value(INIT_ATTRIBUTE_RETURN_VALUE);
    if let Some((ident, _)) = return_value {
        return Err(syn::Error::new(
            ident.span(),
            "The 'return_value' attribute is currently not supported for init methods.",
        ));
    }
    let error = attributes.extract_value(INIT_ATTRIBUTE_ERROR);
    let crypto_primitives = attributes.extract_flag(INIT_ATTRIBUTE_CRYPTO_PRIMITIVES).is_some();

    // Make sure that there are no unrecognized attributes. These would typically be
    // there due to an error. An improvement would be to find the nearest valid one
    // for each of them and report that in the error.
    attributes.report_all_attributes()?;
    Ok(InitAttributes {
        contract,
        optional: OptionalArguments {
            payable,
            enable_logger,
            low_level,
            parameter,
            return_value: None, // Return values are currently not supported on init methods.
            error,
            crypto_primitives,
        },
    })
}

// Supported attributes for the receive methods.

const RECEIVE_ATTRIBUTE_PARAMETER: &str = "parameter";
const RECEIVE_ATTRIBUTE_RETURN_VALUE: &str = "return_value";
const RECEIVE_ATTRIBUTE_ERROR: &str = "error";
const RECEIVE_ATTRIBUTE_CONTRACT: &str = "contract";
const RECEIVE_ATTRIBUTE_NAME: &str = "name";
const RECEIVE_ATTRIBUTE_FALLBACK: &str = "fallback";
const RECEIVE_ATTRIBUTE_PAYABLE: &str = "payable";
const RECEIVE_ATTRIBUTE_ENABLE_LOGGER: &str = "enable_logger";
const RECEIVE_ATTRIBUTE_LOW_LEVEL: &str = "low_level";
const RECEIVE_ATTRIBUTE_MUTABLE: &str = "mutable";
const RECEIVE_ATTRIBUTE_CRYPTO_PRIMITIVES: &str = "crypto_primitives";

fn parse_receive_attributes<'a, I: IntoIterator<Item = &'a Meta>>(
    attrs: I,
) -> syn::Result<ReceiveAttributes> {
    let mut attributes = parse_attributes(attrs)?;

    let contract = attributes.extract_value(RECEIVE_ATTRIBUTE_CONTRACT);
    let name = attributes.extract_ident_and_value(RECEIVE_ATTRIBUTE_NAME);
    let fallback = attributes.extract_flag(RECEIVE_ATTRIBUTE_FALLBACK);
    let parameter: Option<syn::LitStr> = attributes.extract_value(RECEIVE_ATTRIBUTE_PARAMETER);
    let return_value: Option<syn::LitStr> =
        attributes.extract_value(RECEIVE_ATTRIBUTE_RETURN_VALUE);
    let error: Option<syn::LitStr> = attributes.extract_value(RECEIVE_ATTRIBUTE_ERROR);
    let payable = attributes.extract_flag(RECEIVE_ATTRIBUTE_PAYABLE).is_some();
    let enable_logger = attributes.extract_flag(RECEIVE_ATTRIBUTE_ENABLE_LOGGER).is_some();
    let low_level = attributes.extract_flag(RECEIVE_ATTRIBUTE_LOW_LEVEL);
    let mutable = attributes.extract_flag(RECEIVE_ATTRIBUTE_MUTABLE);
    let crypto_primitives = attributes.extract_flag(RECEIVE_ATTRIBUTE_CRYPTO_PRIMITIVES).is_some();

    if let (Some(mutable), Some(low_level)) = (&mutable, &low_level) {
        let mut error = syn::Error::new(
            mutable.span(),
            "The attributes 'mutable' and 'low_level' are incompatible and should not be used on \
             the same method. `mutable` appears here.",
        );
        error.combine(syn::Error::new(
            low_level.span(),
            "The attributes 'mutable' and 'low_level' are incompatible and should not be used on \
             the same method. `low_level` appears here.",
        ));
        return Err(error);
    }

    if let (Some((name, _)), Some(fallback)) = (&name, &fallback) {
        let mut error = syn::Error::new(
            name.span(),
            "The attributes 'name' and 'fallback' are incompatible and should not be used on the \
             same method. `name` appears here.",
        );
        error.combine(syn::Error::new(
            fallback.span(),
            "The attributes 'name' and 'fallback' are incompatible and should not be used on the \
             same method. `fallback` appears here.",
        ));
        return Err(error);
    }
    // Make sure that there are no unrecognized attributes. These would typically be
    // there due to an error. An improvement would be to find the nearest valid one
    // for each of them and report that in the error.
    attributes.report_all_attributes()?;
    match (contract, name) {
        (Some(contract), Some((_, name))) => Ok(ReceiveAttributes {
            contract,
            name,
            optional: OptionalArguments {
                payable,
                enable_logger,
                low_level: low_level.is_some(),
                parameter,
                return_value,
                error,
                crypto_primitives,
            },
            mutable: mutable.is_some(), /* This is also optional, but does not belong in
                                         * OptionalArguments, as
                                         * it doesn't apply to init methods. */
        }),
        (Some(contract), None) => {
            if let Some(ident) = fallback {
                Ok(ReceiveAttributes {
                    contract,
                    name: syn::LitStr::new("", ident.span()),
                    optional: OptionalArguments {
                        payable,
                        enable_logger,
                        low_level: low_level.is_some(),
                        parameter,
                        return_value,
                        error,
                        crypto_primitives,
                    },
                    mutable: mutable.is_some(), /* TODO: This is also optional, but does not
                                                 * belong in
                                                 * OptionalArguments, as
                                                 * it doesn't apply to init methods. */
                })
            } else {
                Err(syn::Error::new(
                    Span::call_site(),
                    "A name for the method must be provided using the 'name' attribute, or the \
                     'fallback' option must be used.\n\nFor example, #[receive(name = \
                     \"receive\")]",
                ))
            }
        }
        (None, Some(_)) => Err(syn::Error::new(
            Span::call_site(),
            "A name for the method must be provided, using the 'contract' attribute.\n\nFor \
             example, #[receive(contract = \"my-contract\")]",
        )),
        (None, None) => Err(syn::Error::new(
            Span::call_site(),
            "A contract name and a name for the method must be provided, using the 'contract' and \
             'name' attributes.\n\nFor example, #[receive(contract = \"my-contract\", name = \
             \"receive\")]",
        )),
    }
}

// Return whether a attribute item is present.
fn contains_attribute<'a, I: IntoIterator<Item = &'a Meta>>(iter: I, name: &str) -> bool {
    iter.into_iter().any(|attr| attr.path().is_ident(name))
}

/// Derive the appropriate export for an annotated init function.
///
/// This macro requires the following items to be present
/// - `contract="<name>"` where *\<name\>* is the name of the smart contract and
///   the generated function is exported as this name prefixed with *init_*. The
///   name should be unique in the module, as a contract can only have one
///   init-function.
///
/// The annotated function must be of a specific type, which depends on the
/// enabled attributes. *Without* any of the optional attributes the function
/// must have a signature of
///
/// ```ignore
/// #[init(contract = "my_contract")]
/// fn some_init<S: HasStateApi>(ctx: &impl HasInitContext, state_builder: &mut StateBuilder<S>,) -> InitResult<MyState> {...}
/// ```
///
/// Where `HasInitContext`, `InitResult`, and `StateBuilder` are exposed from
/// `concordium-std` and `MyState` is a user-defined type.
///
/// # Optional attributes
///
/// ## `payable`: Make function accept an amount of CCD
/// Without setting the `payable` attribute, the generated function will reject
/// any non-zero amount of CCD supplied with the transaction. This means we are
/// required to explicitly mark our functions as `payable`, if they are to
/// accept CCD.
///
/// Setting the `payable` attribute changes the required signature to include an
/// extra argument of type `Amount`, allowing the function to access the amount
/// of CCD supplied with the transaction.
///
/// ### Example
/// ```ignore
/// #[init(contract = "my_contract", payable)]
/// fn some_init<S: HasStateApi>(ctx: &impl HasInitContext, state_builder: StateBuilder<S>, amount: Amount) -> InitResult<MyState> {...}
/// ```
///
/// ## `enable_logger`: Function can access event logging
/// Setting the `enable_logger` attribute changes the required signature to
/// include an extra argument `&mut impl HasLogger`, allowing the function to
/// log events.
///
///
/// ### Example
/// ```ignore
/// #[init(contract = "my_contract", enable_logger)]
/// fn some_init<S: HasStateApi>(ctx: &impl HasInitContext, state_builder: StateBuilder<S>, logger: &mut impl HasLogger) -> InitResult<MyState> {...}
/// ```
///
/// ## `low_level`: Manually deal with the low-level state.
/// Setting the `low_level` attribute disables the generated code for
/// serializing the contract state.
///
/// If `low_level` is set, the `&mut StateBuilder<S>` in the signature is
/// replaced by `&impl mut HasStateApi` found in `concordium-std`, which gives
/// access to manipulating the low-level contract state directly. This means
/// there is no need to return the contract state and the return type becomes
/// `InitResult<()>`.
///
/// ### Example
/// ```ignore
/// #[init(contract = "my_contract", low_level)]
/// fn some_init(ctx: &impl HasInitContext, state: &mut impl HasStateApi) -> InitResult<()> {...}
/// ```
///
/// ## `parameter="<Param>"`: Generate schema for parameter
/// To make schema generation include the parameter for this function, add
/// the attribute `parameter` and set it equal to a string literal containing
/// the name of the type used for the parameter. The parameter type must
/// implement the SchemaType trait, which for most cases can be derived
/// automatically.
///
/// ### Example
/// ```ignore
/// #[derive(SchemaType)]
/// struct MyParam { ... }
///
/// #[init(contract = "my_contract", parameter = "MyParam")]
/// ```
///
/// ## `error="<Error>"`: Generate schema for error
/// To make schema generation include the error for this function, add
/// the attribute `error` and set it equal to a string literal containing
/// the name of the type used for the error. The error type must
/// implement the SchemaType trait, which for most cases can be derived
/// automatically.
///
/// ### Example
/// ```ignore
/// #[derive(SchemaType)]
/// enum MyError { ... }
///
/// #[init(contract = "my_contract", parameter = "MyError")]
/// fn some_init(ctx: &impl HasInitContext, state: &mut impl HasStateApi) -> Result<(), MyError> {...}
/// ```
///
/// ## `crypto_primitives`: Function can access cryptographic primitives
/// Setting the `crypto_primitives` attribute changes the required signature to
/// include an extra argument `&impl HasCryptoPrimitives`, which provides
/// cryptographic primitives such as verifying signatures and hashing data.
///
/// ### Example
/// ```ignore
/// #[init(contract = "my_contract", crypto_primitives)]
/// fn some_init<S: HasStateApi>(
///     ctx: &impl HasInitContext,
///     state_build: StateBuilder<S>,
///     crypto_primitives: &impl HasCryptoPrimitives,
/// ) -> InitResult<MyState> {...}
/// ```
#[proc_macro_attribute]
pub fn init(attr: TokenStream, item: TokenStream) -> TokenStream {
    unwrap_or_report(init_worker(attr, item))
}

fn init_worker(attr: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
    let ast: syn::ItemFn =
        attach_error(syn::parse(item), "#[init] can only be applied to functions.")?;

    let attrs = Punctuated::<Meta, Token![,]>::parse_terminated.parse(attr)?;

    let init_attributes = parse_init_attributes(&attrs)?;

    let contract_name = init_attributes.contract;

    let fn_name = &ast.sig.ident;
    let rust_export_fn_name = format_ident!("export_{}", fn_name);
    let wasm_export_fn_name = format!("init_{}", contract_name.value());

    if let Err(e) = ContractName::is_valid_contract_name(&wasm_export_fn_name) {
        return Err(syn::Error::new(contract_name.span(), e));
    }

    let amount_ident = format_ident!("amount");

    // Accumulate a list of required arguments, if the function contains a
    // different number of arguments, than elements in this vector, then the
    // strings are displayed as the expected arguments.
    let mut required_args = vec!["ctx: &impl HasInitContext"];

    let (setup_fn_optional_args, fn_optional_args) = contract_function_optional_args_tokens(
        &init_attributes.optional,
        &amount_ident,
        &mut required_args,
    );

    let mut out = if init_attributes.optional.low_level {
        required_args.push("state: &mut impl HasStateApi");
        quote! {
            #[export_name = #wasm_export_fn_name]
            pub extern "C" fn #rust_export_fn_name(#amount_ident: concordium_std::Amount) -> i32 {
                use concordium_std::{trap, ExternContext, ExternInitContext, ExternStateApi, HasStateApi};
                #setup_fn_optional_args
                let ctx = ExternContext::<ExternInitContext>::open(());
                let mut state = ExternStateApi::open();
                match #fn_name(&ctx, &mut state, #(#fn_optional_args, )*) {
                    Ok(()) => 0,
                    Err(reject) => {
                        let code = Reject::from(reject).error_code.get();
                        if code < 0 {
                            code
                        } else {
                            trap() // precondition violation
                        }
                    }
                }
            }
        }
    } else {
        required_args.push("state_builder: &mut StateBuilder");
        quote! {
            #[export_name = #wasm_export_fn_name]
            pub extern "C" fn #rust_export_fn_name(amount: concordium_std::Amount) -> i32 {
                use concordium_std::{trap, ExternContext, ExternInitContext, StateBuilder, ExternReturnValue};
                #setup_fn_optional_args
                let ctx = ExternContext::<ExternInitContext>::open(());
                let mut state_api = ExternStateApi::open();
                let mut state_builder = StateBuilder::open(state_api.clone());
                match #fn_name(&ctx, &mut state_builder, #(#fn_optional_args, )*) {
                    Ok(state) => {
                        // Store the state.
                        let mut root_entry = state_api.create_entry(&[]).unwrap_abort();
                        state.serial(&mut root_entry).unwrap_abort();
                        // Return success
                        0
                    },
                    Err(reject) => {
                        let code = Reject::from(reject).error_code.get();
                        if code < 0 {
                            code
                        } else {
                            trap() // precondition violation
                        }
                    }
                }
            }
        }
    };

    let arg_count = ast.sig.inputs.len();
    if arg_count != required_args.len() {
        return Err(syn::Error::new(
            ast.sig.inputs.span(),
            format!(
                "Incorrect number of function arguments, the expected arguments are ({}) ",
                required_args.join(", ")
            ),
        ));
    }

    // Embed a schema for the parameter and return value if the corresponding
    // attribute is set.
    let parameter_option = init_attributes.optional.parameter;
    let return_value_option = None; // Return values are currently not supported on init.
    let error_option = init_attributes.optional.error;
    out.extend(contract_function_schema_tokens(
        parameter_option,
        return_value_option,
        error_option,
        rust_export_fn_name,
        wasm_export_fn_name,
    )?);

    ast.to_tokens(&mut out);

    Ok(out.into())
}

/// Derive the appropriate export for an annotated receive function.
///
/// This macro requires the following items to be present
/// - `contract = "<contract-name>"` where *\<contract-name\>* is the name of
///   the smart contract.
/// - `name = "<receive-name>"` where *\<receive-name\>* is the name of the
///   receive function, **or** the `fallback` option. The generated function is
///   exported as `<contract-name>.<receive-name>`, or if `fallback` is given,
///   as `<contract-name>.`.Contract name and receive name is required to be
///   unique in the module. In particular, a contract may have only a single
///   fallback method.
///
/// The annotated function must be of a specific type, which depends on the
/// enabled attributes. *Without* any of the optional attributes the function
/// must have a signature of
///
/// ```ignore
/// #[receive(contract = "my_contract", name = "some_receive")]
/// fn contract_receive<S: HasStateApi>(
///     ctx: &impl HasReceiveContext,
///     host: &HasHost<MyState, StateApiType = S>
/// ) -> ReceiveResult<MyReturnValue> {...}
/// ```
///
/// Where the `HasStateApi`, `HasReceiveContext`, `HasHost`, and `ReceiveResult`
/// are from `concordium-std` and `MyState` and `MyReturnValue` are user-defined
/// types.
///
/// # Optional attributes
///
/// ## `payable`: Make function accept an amount of CCD
/// Without setting the `payable` attribute, the function will reject any
/// non-zero amount of CCD, supplied with the transaction. This means we are
/// required to explicitly mark our functions as `payable`, if they are to
/// accept CCD.
///
/// Setting the `payable` attribute changes the required signature to include an
/// extra argument of type `Amount`, allowing the function to access the amount
/// of CCD supplied with the transaction.
///
/// ### Example
/// ```ignore
/// #[receive(contract = "my_contract", name = "some_receive", payable)]
/// fn contract_receive<S: HasStateApi>(
///     ctx: &impl HasReceiveContext,
///     host: &HasHost<MyState, StateApiType = S>,
///     amount: Amount
/// ) -> ReceiveResult<MyReturnValue> {...}
/// ```
///
/// ## `mutable`: Function can mutate the state
/// Setting the `mutable` attribute changes the required signature so the host
/// becomes a mutable reference.
///
/// **When a receive method is mutable, the state, e.g. `MyState`, is serialized
/// and stored after each invocation. This means that even if the state does
/// not change semantically, it will be considered as modified by callers.**
/// Thus the `mutable` option should only be used when absolutely necessary.
///
/// ### Example
/// ```ignore
/// #[receive(contract = "my_contract", name = "some_receive", mutable)]
/// fn contract_receive<S: HasStateApi>(
///     ctx: &impl HasReceiveContext,
///     host: &mut HasHost<MyState, StateApiType = S>
/// ) -> ReceiveResult<MyReturnValue> {...}
/// ```
///
/// ## `enable_logger`: Function can access event logging
/// Setting the `enable_logger` attribute changes the required signature to
/// include an extra argument `&mut impl HasLogger`, allowing the function to
/// log events.
///
/// ### Example
/// ```ignore
/// #[receive(contract = "my_contract", name = "some_receive", enable_logger)]
/// fn contract_receive<S: HasStateApi>(
///     ctx: &impl HasReceiveContext,
///     host: &HasHost<MyState, StateApiType = S>,
///     logger: &mut impl HasLogger
/// ) -> ReceiveResult<MyReturnValue> {...}
/// ```
///
/// ## `low_level`: Manually deal with the low-level state including writing
/// bytes Setting the `low_level` attribute disables the generated code for
/// serializing the contract state. However, the return value is still
/// serialized automatically.
///
/// If `low_level` is set, the `&mut StateBuilder<S>` in the signature is
/// replaced by `&impl mut HasStateApi` found in `concordium-std`, which gives
/// access to manipulating the low-level contract state directly.
///
/// ### Example
/// ```ignore
/// #[receive(contract = "my_contract", name = "some_receive", low_level)]
/// fn contract_receive(
///     ctx: &impl HasReceiveContext,
///     state: &mut impl HasStateApi
/// ) -> ReceiveResult<MyReturnValue> {...}
/// ```
///
/// ## `parameter="<Param>"`: Generate schema for parameter
/// To make schema generation include the parameter for this function, add
/// the attribute `parameter` and set it equal to a string literal containing
/// the type used for the parameter. The parameter type must
/// implement the SchemaType trait, which for most cases can be derived
/// automatically.
///
/// ### Example
/// ```ignore
/// #[derive(SchemaType)]
/// struct MyParam { ... }
///
/// #[receive(contract = "my_contract", name = "some_receive", parameter = "MyParam")]
/// fn contract_receive<S: HasStateApi>(
///     ctx: &impl HasReceiveContext,
///     host: &HasHost<MyState, StateApiType = S>,
/// ) -> ReceiveResult<A> {...}
/// ```
///
/// ## `return_value="<ReturnValue>"`: Generate schema for the return value.
/// To make schema generation include the return value for this function, add
/// the attribute `return_value` and set it equal to a string literal containing
/// the type used for the parameter. The parameter type must
/// implement the SchemaType trait, which for most cases can be derived
/// automatically.
///
/// ### Example
///
/// ```ignore
/// #[derive(SchemaType)]
/// struct MyReturnValue { ... }
///
/// #[receive(contract = "my_contract", name = "some_receive", return_value = "MyReturnValue")]
/// fn contract_receive<S: HasStateApi>(
///    ctx: &impl HasReceiveContext,
///    host: &HasHost<MyState, StateApiType = S>,
/// ) -> ReceiveResult<MyReturnValue> {...}
/// ```
///
/// ## `error="<Error>"`: Generate schema for error
/// To make schema generation include the error for this function, add
/// the attribute `error` and set it equal to a string literal containing
/// the type used for the error. The error type must
/// implement the SchemaType trait, which for most cases can be derived
/// automatically.
///
/// ### Example
/// ```ignore
/// #[derive(SchemaType)]
/// enum MyError { ... }
///
/// #[receive(contract = "my_contract", name = "some_receive", error = "MyError")]
/// fn contract_receive<S: HasStateApi>(
///     ctx: &impl HasReceiveContext,
///     host: &HasHost<MyState, StateApiType = S>,
/// ) -> Result<A, MyError> {...}
/// ```
///
/// ## `fallback`: Create a fallback entrypoint.
/// A contract can have a *single* fallback entrypoint defined.
/// If defined, invocations on missing entrypoint will be redirected to the
/// fallback entrypoint. For fallback entrypoints, the `name` attribute is not
/// allowed. This is because fallback entrypoints always have the empty string
/// as their name.
///
/// To get the name of the entrypoint used for invocation, use
/// `ctx.named_entrypoint()`. The method is available in all receive methods,
/// but is only useful on fallback entrypoints.
///
/// ### Example
/// ```ignore
/// #[receive(contract = "my_contract", fallback)]
/// fn contract_receive<S: HasStateApi>(
///    ctx: &impl HasReceiveContext,
///    host: &HasHost<MyState, StateApiType = S>,
/// ) -> ReceiveResult<MyReturnValue> {
///     let named_entrypoint = ctx.named_entrypoint();
///     // ...
/// }
/// ```
/// ## `crypto_primitives`: Function can access cryptographic primitives
/// Setting the `crypto_primitives` attribute changes the required signature to
/// include an extra argument `&impl HasCryptoPrimitives`, which provides
/// cryptographic primitives such as verifying signatures and hashing data.
///
/// ### Example
/// ```ignore
/// #[receive(contract = "my_contract", name = "some_receive", crypto_primitives)]
/// fn some_receive<S: HasStateApi>(
///     ctx: &impl HasReceiveContext,
///     host: &impl HasHost<MyState, StateApiType = S>,
///     crypto_primitives: &impl HasCryptoPrimitives,
/// ) -> ReceiveResult<MyReturnValue> {...}
/// ```
#[proc_macro_attribute]
pub fn receive(attr: TokenStream, item: TokenStream) -> TokenStream {
    unwrap_or_report(receive_worker(attr, item))
}

fn receive_worker(attr: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
    let ast: syn::ItemFn =
        attach_error(syn::parse(item), "#[receive] can only be applied to functions.")?;

    let attrs = Punctuated::<Meta, Token![,]>::parse_terminated.parse(attr)?;

    let receive_attributes = parse_receive_attributes(&attrs)?;

    let contract_name = receive_attributes.contract;

    let method_name = receive_attributes.name;

    let fn_name = &ast.sig.ident;
    let rust_export_fn_name = format_ident!("export_{}", fn_name);
    let wasm_export_fn_name = format!("{}.{}", contract_name.value(), method_name.value());

    // Validate the contract name independently to ensure that it doesn't contain a
    // '.' as this causes a subtle error when receive names are being split.
    let contract_name_validation =
        ContractName::is_valid_contract_name(&format!("init_{}", contract_name.value()))
            .map_err(|e| syn::Error::new(contract_name.span(), e));

    let receive_name_validation = ReceiveName::is_valid_receive_name(&wasm_export_fn_name)
        .map_err(|e| syn::Error::new(method_name.span(), e));

    match (contract_name_validation, receive_name_validation) {
        (Err(mut e0), Err(e1)) => {
            e0.combine(e1);
            return Err(e0);
        }
        (Err(e), _) => return Err(e),
        (_, Err(e)) => return Err(e),
        _ => (),
    };

    let amount_ident = format_ident!("amount");

    // Accumulate a list of required arguments, if the function contains a
    // different number of arguments, than elements in this vector, then the
    // strings are displayed as the expected arguments.
    let mut required_args = vec!["ctx: &impl HasReceiveContext"];
    if receive_attributes.mutable {
        required_args.push("host: &mut impl HasHost");
    } else {
        required_args.push("host: &impl HasHost");
    }

    let (setup_fn_optional_args, fn_optional_args) = contract_function_optional_args_tokens(
        &receive_attributes.optional,
        &amount_ident,
        &mut required_args,
    );

    let mut out = if receive_attributes.optional.low_level {
        quote! {
            #[export_name = #wasm_export_fn_name]
            pub extern "C" fn #rust_export_fn_name(#amount_ident: concordium_std::Amount) -> i32 {
                use concordium_std::{SeekFrom, Logger, ExternReceiveContext, ExternContext, ExternLowLevelHost};
                #setup_fn_optional_args
                let ctx = ExternContext::<ExternReceiveContext>::open(());
                let mut host = ExternLowLevelHost::default();
                match #fn_name(&ctx, &mut host, #(#fn_optional_args, )*) {
                    Ok(rv) => {
                        if rv.serial(&mut ExternReturnValue::open()).is_err() {
                            trap() // Could not serialize the return value.
                        }
                        0
                    }
                    Err(reject) => {
                        let reject = Reject::from(reject);
                        let code = reject.error_code.get();
                        if code < 0 {
                            if let Some(rv) = reject.return_value {
                                if ExternReturnValue::open().write_all(&rv).is_err() {
                                    trap() // Could not serialize the return value.
                                }
                            }
                            code
                        } else {
                            trap() // precondition violation
                        }
                    }
                }
            }
        }
    } else {
        let (host_ref, save_state_if_mutable) = if receive_attributes.mutable {
            (quote!(&mut host), quote! {
                // look up the root entry again, since we might be in a different generation now
                let mut root_entry_end = host.state_builder.into_inner().lookup_entry(&[]).unwrap_abort();
                host.state.serial(&mut root_entry_end).unwrap_abort();
                let new_state_size = root_entry_end.size().unwrap_abort();
                root_entry_end.truncate(new_state_size).unwrap_abort();
            })
        } else {
            (quote!(&host), quote!())
        };

        quote! {
            #[export_name = #wasm_export_fn_name]
            pub extern "C" fn #rust_export_fn_name(#amount_ident: concordium_std::Amount) -> i32 {
                use concordium_std::{SeekFrom, StateBuilder, Logger, ExternHost, trap};
                #setup_fn_optional_args
                let ctx = ExternContext::<ExternReceiveContext>::open(());
                let state_api = ExternStateApi::open();
                if let Ok(state) = DeserialWithState::deserial_with_state(&state_api, &mut state_api.lookup_entry(&[]).unwrap_abort()) {
                    let mut state_builder = StateBuilder::open(state_api);
                    let mut host = ExternHost { state, state_builder };
                    match #fn_name(&ctx, #host_ref, #(#fn_optional_args, )*) {
                        Ok(rv) => {
                            if rv.serial(&mut ExternReturnValue::open()).is_err() {
                                trap() // Could not serialize return value.
                            }
                            #save_state_if_mutable
                            0
                        }
                        Err(reject) => {
                            let reject = Reject::from(reject);
                            let code = reject.error_code.get();
                            if code < 0 {
                                if let Some(rv) = reject.return_value {
                                    if ExternReturnValue::open().write_all(&rv).is_err() {
                                        trap() // Could not serialize the return value.
                                    }
                                }
                                code
                            } else {
                                trap() // precondition violation
                            }
                        }
                    }
                } else {
                    trap() // Could not fully read state.
                }
            }
        }
    };

    let arg_count = ast.sig.inputs.len();
    if arg_count != required_args.len() {
        return Err(syn::Error::new(
            ast.sig.inputs.span(),
            format!(
                "Incorrect number of function arguments, the expected arguments are ({}) ",
                required_args.join(", ")
            ),
        ));
    }

    // Embed a schema for the parameter and return value if the corresponding
    // attribute is set.
    let parameter_option = receive_attributes.optional.parameter;
    let return_value_option = receive_attributes.optional.return_value;
    let error_option = receive_attributes.optional.error;
    out.extend(contract_function_schema_tokens(
        parameter_option,
        return_value_option,
        error_option,
        rust_export_fn_name,
        wasm_export_fn_name,
    )?);
    // add the original function to the output as well.
    ast.to_tokens(&mut out);
    Ok(out.into())
}

/// Generate tokens for some of the optional arguments, based on the attributes.
/// Returns a pair, where the first entry is tokens for setting up the arguments
/// and the second entry is a Vec of the argument names as tokens.
///
/// It also mutates a vector of required arguments with the expected type
/// signature of each.
fn contract_function_optional_args_tokens(
    optional: &OptionalArguments,
    amount_ident: &syn::Ident,
    required_args: &mut Vec<&str>,
) -> (proc_macro2::TokenStream, Vec<proc_macro2::TokenStream>) {
    let mut setup_fn_args = proc_macro2::TokenStream::new();
    let mut fn_args = vec![];
    if optional.payable {
        required_args.push("amount: Amount");
        fn_args.push(quote!(#amount_ident));
    } else {
        setup_fn_args.extend(quote! {
            if #amount_ident.micro_ccd != 0 {
                return concordium_std::Reject::from(concordium_std::NotPayableError).error_code.get();
            }
        });
    };

    if optional.enable_logger {
        required_args.push("logger: &mut impl HasLogger");
        let logger_ident = format_ident!("logger");
        setup_fn_args.extend(quote!(let mut #logger_ident = concordium_std::Logger::init();));
        fn_args.push(quote!(&mut #logger_ident));
    }

    if optional.crypto_primitives {
        required_args.push("crypto_primitives: &impl HasCryptoPrimitives");
        let crypto_primitives_ident = format_ident!("crypto_primitives");
        setup_fn_args
            .extend(quote!(let #crypto_primitives_ident = concordium_std::ExternCryptoPrimitives;));
        fn_args.push(quote!(&#crypto_primitives_ident));
    }

    (setup_fn_args, fn_args)
}

#[cfg(feature = "build-schema")]
fn contract_function_schema_tokens(
    parameter_option: Option<syn::LitStr>,
    return_value_option: Option<syn::LitStr>,
    error_option: Option<syn::LitStr>,
    rust_name: syn::Ident,
    wasm_name: String,
) -> syn::Result<proc_macro2::TokenStream> {
    let construct_schema_bytes = match (parameter_option, return_value_option, error_option) {
        (Some(parameter_ty), None, None) => {
            let parameter_ty = parameter_ty.parse::<syn::Type>()?;
            Some(quote! {
            let parameter = <#parameter_ty as schema::SchemaType>::get_type();
            let schema_bytes = concordium_std::to_bytes(&schema::FunctionV2::Param(parameter));})
        }
        (None, Some(return_value_ty), None) => {
            let return_value_ty = return_value_ty.parse::<syn::Type>()?;
            Some(quote! {
            let return_value = <#return_value_ty as schema::SchemaType>::get_type();
            let schema_bytes =
                concordium_std::to_bytes(&schema::FunctionV2::Rv(return_value));     })
        }
        (Some(parameter_ty), Some(return_value_ty), None) => {
            let parameter_ty = parameter_ty.parse::<syn::Type>()?;
            let return_value_ty = return_value_ty.parse::<syn::Type>()?;
            Some(quote! {
                    let parameter = <#parameter_ty as schema::SchemaType>::get_type();
                    let return_value = <#return_value_ty as schema::SchemaType>::get_type();
                    let schema_bytes = concordium_std::to_bytes(&schema::FunctionV2::ParamRv {
            parameter, return_value });     })
        }
        (None, None, Some(error_ty)) => {
            let error_ty = error_ty.parse::<syn::Type>()?;
            Some(quote! {
            let error = <#error_ty as schema::SchemaType>::get_type();
            let schema_bytes = concordium_std::to_bytes(&schema::FunctionV2::Error(error));     })
        }
        (Some(parameter_ty), None, Some(error_ty)) => {
            let parameter_ty = parameter_ty.parse::<syn::Type>()?;
            let error_ty = error_ty.parse::<syn::Type>()?;
            Some(quote! {
                    let parameter = <#parameter_ty as schema::SchemaType>::get_type();
                    let error = <#error_ty as schema::SchemaType>::get_type();
                    let schema_bytes = concordium_std::to_bytes(&schema::FunctionV2::ParamError {
            parameter, error });     })
        }
        (None, Some(return_value_ty), Some(error_ty)) => {
            let return_value_ty = return_value_ty.parse::<syn::Type>()?;
            let error_ty = error_ty.parse::<syn::Type>()?;
            Some(quote! {
                    let return_value = <#return_value_ty as schema::SchemaType>::get_type();
                    let error = <#error_ty as schema::SchemaType>::get_type();
                    let schema_bytes = concordium_std::to_bytes(&schema::FunctionV2::RvError {
            return_value, error });     })
        }
        (Some(parameter_ty), Some(return_value_ty), Some(error_ty)) => {
            let parameter_ty = parameter_ty.parse::<syn::Type>()?;
            let return_value_ty = return_value_ty.parse::<syn::Type>()?;
            let error_ty = error_ty.parse::<syn::Type>()?;
            Some(quote! {
                    let parameter = <#parameter_ty as schema::SchemaType>::get_type();
                    let return_value = <#return_value_ty as schema::SchemaType>::get_type();
                    let error = <#error_ty as schema::SchemaType>::get_type();
                    let schema_bytes = concordium_std::to_bytes(&schema::FunctionV2::ParamRvError {
            parameter, return_value, error });     })
        }
        _ => None,
    };

    // Only produce the schema function if the parameter or return_value attribute
    // was set.
    if let Some(construct_schema_bytes) = construct_schema_bytes {
        let schema_name = format!("concordium_schema_function_{}", wasm_name);
        let schema_ident = format_ident!("concordium_schema_function_{}", rust_name);
        Ok(quote! {
            #[export_name = #schema_name]
            pub extern "C" fn #schema_ident() -> *mut u8 {
                #construct_schema_bytes
                concordium_std::put_in_memory(&schema_bytes)
            }
        })
    } else {
        Ok(proc_macro2::TokenStream::new())
    }
}

#[cfg(not(feature = "build-schema"))]
fn contract_function_schema_tokens(
    _parameter_option: Option<syn::LitStr>,
    _return_value_option: Option<syn::LitStr>,
    _error_option: Option<syn::LitStr>,
    _rust_name: syn::Ident,
    _wasm_name: String,
) -> syn::Result<proc_macro2::TokenStream> {
    Ok(proc_macro2::TokenStream::new())
}

/// The prefix used in field attributes: `#[concordium(attr = "something")]`
const CONCORDIUM_ATTRIBUTE: &str = "concordium";

/// A list of valid concordium field attributes
const VALID_CONCORDIUM_FIELD_ATTRIBUTES: [&str; 3] = ["size_length", "ensure_ordered", "rename"];

/// A list of valid concordium attributes
const VALID_CONCORDIUM_ATTRIBUTES: [&str; 1] = ["state_parameter"];

/// Finds concordium field attributes.
fn get_concordium_field_attributes(attributes: &[syn::Attribute]) -> syn::Result<Vec<syn::Meta>> {
    get_concordium_attributes(attributes, true)
}

/// Finds concordium attributes, either field or general attributes.
fn get_concordium_attributes(
    attributes: &[syn::Attribute],
    for_field: bool,
) -> syn::Result<Vec<syn::Meta>> {
    let (valid_attributes, attribute_type) = if for_field {
        (&VALID_CONCORDIUM_FIELD_ATTRIBUTES[..], "concordium field attribute")
    } else {
        (&VALID_CONCORDIUM_ATTRIBUTES[..], "concordium attribute")
    };

    attributes
        .iter()
        // Keep only concordium attributes
        .flat_map(|attr| match attr.parse_meta() {
            Ok(syn::Meta::List(list)) if list.path.is_ident(CONCORDIUM_ATTRIBUTE) => {
                list.nested
            }
            _ => syn::punctuated::Punctuated::new(),
        })
        // Ensure only valid attributes and unwrap NestedMeta
        .map(|nested| match nested {
            syn::NestedMeta::Meta(meta) => {
                let path = meta.path();
                if valid_attributes.iter().any(|&attr| path.is_ident(attr)) {
                    Ok(meta)
                } else {
                    Err(syn::Error::new(meta.span(),
                        format!("The attribute '{}' is not supported as a {}.",
                        path.to_token_stream(), attribute_type)
                    ))
                }
            }
            lit => Err(syn::Error::new(lit.span(), format!("Literals are not supported in a {}.", attribute_type))),
        })
        .collect()
}

fn find_field_attribute_value(
    attributes: &[syn::Attribute],
    target_attr: &str,
) -> syn::Result<Option<syn::Lit>> {
    find_attribute_value(attributes, true, target_attr)
}

fn find_attribute_value(
    attributes: &[syn::Attribute],
    for_field: bool,
    target_attr: &str,
) -> syn::Result<Option<syn::Lit>> {
    let target_attr = format_ident!("{}", target_attr);
    let attr_values: Vec<_> = get_concordium_attributes(attributes, for_field)?
        .into_iter()
        .filter_map(|nested_meta| match nested_meta {
            syn::Meta::NameValue(value) if value.path.is_ident(&target_attr) => Some(value.lit),
            _ => None,
        })
        .collect();
    if attr_values.is_empty() {
        return Ok(None);
    }
    if attr_values.len() > 1 {
        let mut init_error = syn::Error::new(
            attr_values[1].span(),
            format!("Attribute '{}' should only be specified once.", target_attr),
        );
        for other in attr_values.iter().skip(2) {
            init_error.combine(syn::Error::new(
                other.span(),
                format!("Attribute '{}' should only be specified once.", target_attr),
            ))
        }
        Err(init_error)
    } else {
        Ok(Some(attr_values[0].clone()))
    }
}

fn find_length_attribute(attributes: &[syn::Attribute]) -> syn::Result<Option<u32>> {
    let value = match find_field_attribute_value(attributes, "size_length")? {
        Some(v) => v,
        None => return Ok(None),
    };

    // Save the span to be used in errors.
    let value_span = value.span();

    let value = match value {
        syn::Lit::Int(int) => int,
        _ => return Err(syn::Error::new(value_span, "Length attribute value must be an integer.")),
    };
    let value = match value.base10_parse() {
        Ok(v) => v,
        _ => {
            return Err(syn::Error::new(
                value_span,
                "Length attribute value must be a base 10 integer.",
            ))
        }
    };
    match value {
        1 | 2 | 4 | 8 => Ok(Some(value)),
        _ => Err(syn::Error::new(value_span, "Length info must be either 1, 2, 4, or 8.")),
    }
}

/// Find a 'state_parameter' attribute and return it as an identifier.
/// Checks that the attribute is only defined once and that the value is a
/// string.
fn find_state_parameter_attribute(
    attributes: &[syn::Attribute],
) -> syn::Result<Option<syn::Ident>> {
    let value = match find_attribute_value(attributes, false, "state_parameter")? {
        Some(v) => v,
        None => return Ok(None),
    };

    match value {
        syn::Lit::Str(value) => Ok(Some(syn::Ident::new(&value.value(), value.span()))),
        _ => {
            Err(syn::Error::new(value.span(), "state_parameter attribute value must be a string."))
        }
    }
}

/// Find a 'rename' attribute and return its value and span.
/// Checks that the attribute is only defined once and that the value is a
/// string.
#[cfg(feature = "build-schema")]
fn find_rename_attribute(attributes: &[syn::Attribute]) -> syn::Result<Option<(String, Span)>> {
    let value = match find_field_attribute_value(attributes, "rename")? {
        Some(v) => v,
        None => return Ok(None),
    };

    match value {
        syn::Lit::Str(value) => Ok(Some((value.value(), value.span()))),
        _ => Err(syn::Error::new(value.span(), "Rename attribute value must be a string.")),
    }
}

/// Check for name collisions by inserting the name in the HashMap.
/// On collisions it returns a combined error pointing to the previous and new
/// definition.
#[cfg(feature = "build-schema")]
fn check_for_name_collisions(
    used_names: &mut HashMap<String, Span>,
    new_name: &str,
    new_span: Span,
) -> syn::Result<()> {
    if let Some(used_span) = used_names.insert(String::from(new_name), new_span) {
        let error_msg = format!("the name `{}` is defined multiple times", new_name);
        let mut error_at_first_def = syn::Error::new(used_span, &error_msg);
        let error_at_second_def = syn::Error::new(new_span, &error_msg);

        // Combine the errors to show both at once
        error_at_first_def.combine(error_at_second_def);

        return Err(error_at_first_def);
    }
    Ok(())
}

/// Derive the DeserialWithState trait. See the documentation of
/// [`derive(Deserial)`](./derive.Deserial.html) for details and limitations.
///
/// This trait should be derived for `struct`s or `enum`s that have fields with
/// [`StateBox`](../concordium_std/struct.StateBox.html),
/// [`StateSet`](../concordium_std/struct.StateSet.html), or
/// [`StateMap`](../concordium_std/struct.StateMap.html). Please note that it is
/// necessary to specify the generic parameter name for the
/// [`HasStateApi`](../concordium_std/trait.HasStateApi.html) generic parameter.
/// To do so, use the `#[concordium(state_parameter =
/// "NameOfGenericParameter")]` attribute on the type you are deriving
/// `DeserialWithState` for.
///
/// # Example
/// ``` ignore
/// #[derive(DeserialWithState)]
/// #[concordium(state_parameter = "S")]
/// struct Foo<S, T> {
///     a: StateMap<u8, u8, S>,
///     #[concordium(size_length = 1)]
///     b: String,
///     c: Vec<T>,
/// }
/// ```
#[proc_macro_derive(DeserialWithState, attributes(concordium))]
pub fn deserial_with_state_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input);
    unwrap_or_report(impl_deserial_with_state(&ast))
}

fn impl_deserial_with_state_field(
    f: &syn::Field,
    state_ident: &syn::Ident,
    ident: &syn::Ident,
    source: &syn::Ident,
    state_parameter: &syn::Ident,
) -> syn::Result<proc_macro2::TokenStream> {
    let concordium_attributes = get_concordium_field_attributes(&f.attrs)?;
    let ensure_ordered = contains_attribute(&concordium_attributes, "ensure_ordered");
    let size_length = find_length_attribute(&f.attrs)?;
    let has_ctx = ensure_ordered || size_length.is_some();
    let ty = &f.ty;
    if has_ctx {
        // Default size length is u32, i.e. 4 bytes.
        let l = format_ident!("U{}", 8 * size_length.unwrap_or(4));
        Ok(quote! {
            let #ident = <#ty as concordium_std::DeserialCtxWithState<#state_parameter>>::deserial_ctx_with_state(concordium_std::schema::SizeLength::#l, #ensure_ordered, #state_ident, #source)?;
        })
    } else {
        Ok(quote! {
            let #ident = <#ty as concordium_std::DeserialWithState<#state_parameter>>::deserial_with_state(#state_ident, #source)?;
        })
    }
}

fn impl_deserial_with_state(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let data_name = &ast.ident;
    let span = ast.span();
    let read_ident = format_ident!("__R", span = span);
    let state_parameter = match find_state_parameter_attribute(&ast.attrs)? {
        Some(state_parameter) => state_parameter,
        None => {
            return Err(syn::Error::new(
                Span::call_site(),
                "DeriveWithState requires the attribute #[concordium(state_parameter = \"S\")], \
                 where \"S\" should be the generic parameter satisfying `HasStateApi`.",
            ))
        }
    };
    let (impl_generics, ty_generics, where_clauses) = ast.generics.split_for_impl();
    let where_predicates = where_clauses.map(|c| c.predicates.clone());

    let source_ident = Ident::new("________________source", Span::call_site());

    let state_ident = Ident::new("_______________________________state", Span::call_site());
    let body_tokens = match ast.data {
        syn::Data::Struct(ref data) => {
            let mut names = proc_macro2::TokenStream::new();
            let mut field_tokens = proc_macro2::TokenStream::new();
            let return_tokens = match data.fields {
                syn::Fields::Named(_) => {
                    for field in data.fields.iter() {
                        let field_ident = field.ident.clone().unwrap(); // safe since named fields.
                        field_tokens.extend(impl_deserial_with_state_field(
                            field,
                            &state_ident,
                            &field_ident,
                            &source_ident,
                            &state_parameter,
                        ));
                        names.extend(quote!(#field_ident,))
                    }
                    quote!(Ok(#data_name{#names}))
                }
                syn::Fields::Unnamed(_) => {
                    for (i, f) in data.fields.iter().enumerate() {
                        let field_ident = format_ident!("x_{}", i);
                        field_tokens.extend(impl_deserial_with_state_field(
                            f,
                            &state_ident,
                            &field_ident,
                            &source_ident,
                            &state_parameter,
                        ));
                        names.extend(quote!(#field_ident,))
                    }
                    quote!(Ok(#data_name(#names)))
                }
                _ => quote!(Ok(#data_name{})),
            };
            quote! {
                #field_tokens
                #return_tokens
            }
        }
        syn::Data::Enum(ref data) => {
            let mut matches_tokens = proc_macro2::TokenStream::new();
            let source = Ident::new("________________source", Span::call_site());
            let size = if data.variants.len() <= 256 {
                format_ident!("u8")
            } else if data.variants.len() <= 256 * 256 {
                format_ident!("u16")
            } else {
                return Err(syn::Error::new(
                    ast.span(),
                    "[derive(DeserialWithState)]: Too many variants. Maximum 65536 are supported.",
                ));
            };
            let state_ident = Ident::new("_______________________________state", Span::call_site());
            for (i, variant) in data.variants.iter().enumerate() {
                let (field_names, pattern) = match variant.fields {
                    syn::Fields::Named(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .map(|field| field.ident.clone().unwrap())
                            .collect();
                        (field_names.clone(), quote! { {#(#field_names),*} })
                    }
                    syn::Fields::Unnamed(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, _)| format_ident!("x_{}", i))
                            .collect();
                        (field_names.clone(), quote! { ( #(#field_names),* ) })
                    }
                    syn::Fields::Unit => (Vec::new(), proc_macro2::TokenStream::new()),
                };
                let field_tokens: proc_macro2::TokenStream = field_names
                    .iter()
                    .zip(variant.fields.iter())
                    .map(|(name, field)| {
                        impl_deserial_with_state_field(
                            field,
                            &state_ident,
                            name,
                            &source,
                            &state_parameter,
                        )
                    })
                    .collect::<syn::Result<proc_macro2::TokenStream>>()?;
                let idx_lit = syn::LitInt::new(i.to_string().as_str(), Span::call_site());
                let variant_ident = &variant.ident;
                matches_tokens.extend(quote! {
                    #idx_lit => {
                        #field_tokens
                        Ok(#data_name::#variant_ident#pattern)
                    },
                })
            }
            quote! {
                let idx = #size::deserial(#source)?;
                match idx {
                    #matches_tokens
                    _ => Err(Default::default())
                }
            }
        }
        _ => unimplemented!("#[derive(DeserialWithState)] is not implemented for union."),
    };
    let gen = quote! {
        #[automatically_derived]
        impl #impl_generics DeserialWithState<#state_parameter> for #data_name #ty_generics where #state_parameter : HasStateApi, #where_predicates {
            fn deserial_with_state<#read_ident: Read>(#state_ident: &#state_parameter, #source_ident: &mut #read_ident) -> ParseResult<Self> {
                #body_tokens
            }
        }
    };
    Ok(gen.into())
}

/// Derive the `SchemaType` trait for a type.
/// If the feature `build-schema` is not enabled this is a no-op, i.e., it does
/// not produce any code.
#[proc_macro_derive(SchemaType, attributes(size_length))]
pub fn schema_type_derive(input: TokenStream) -> TokenStream {
    unwrap_or_report(schema_type_derive_worker(input))
}

#[cfg(feature = "build-schema")]
fn schema_type_derive_worker(input: TokenStream) -> syn::Result<TokenStream> {
    let ast: syn::DeriveInput = syn::parse(input)?;

    let data_name = &ast.ident;

    let (impl_generics, ty_generics, where_clauses) = ast.generics.split_for_impl();

    let body = match ast.data {
        syn::Data::Struct(ref data) => {
            let fields_tokens = schema_type_fields(&data.fields)?;
            quote! {
                concordium_std::schema::Type::Struct(#fields_tokens)
            }
        }
        syn::Data::Enum(ref data) => {
            let mut used_variant_names = HashMap::new();
            let variant_tokens: Vec<_> = data
                .variants
                .iter()
                .map(|variant| {
                    // Handle the 'rename' attribute.
                    let (variant_name, variant_span) = match find_rename_attribute(&variant.attrs)?
                    {
                        Some(name_and_span) => name_and_span,
                        None => (variant.ident.to_string(), variant.ident.span()),
                    };
                    check_for_name_collisions(
                        &mut used_variant_names,
                        &variant_name,
                        variant_span,
                    )?;

                    let fields_tokens = schema_type_fields(&variant.fields)?;
                    Ok(quote! {
                        (concordium_std::String::from(#variant_name), #fields_tokens)
                    })
                })
                .collect::<syn::Result<_>>()?;
            quote! {
                concordium_std::schema::Type::Enum(concordium_std::Vec::from([ #(#variant_tokens),* ]))
            }
        }
        _ => syn::Error::new(ast.span(), "Union is not supported").to_compile_error(),
    };

    let out = quote! {
        #[automatically_derived]
        impl #impl_generics concordium_std::schema::SchemaType for #data_name #ty_generics #where_clauses {
            fn get_type() -> concordium_std::schema::Type {
                #body
            }
        }
    };
    Ok(out.into())
}

#[cfg(not(feature = "build-schema"))]
fn schema_type_derive_worker(_input: TokenStream) -> syn::Result<TokenStream> {
    Ok(TokenStream::new())
}

#[cfg(feature = "build-schema")]
fn schema_type_field_type(field: &syn::Field) -> syn::Result<proc_macro2::TokenStream> {
    let field_type = &field.ty;
    if let Some(l) = find_length_attribute(&field.attrs)? {
        let size = format_ident!("U{}", 8 * l);
        Ok(quote! {
            <#field_type as concordium_std::schema::SchemaType>::get_type().set_size_length(concordium_std::schema::SizeLength::#size)
        })
    } else {
        Ok(quote! {
            <#field_type as concordium_std::schema::SchemaType>::get_type()
        })
    }
}

#[cfg(feature = "build-schema")]
fn schema_type_fields(fields: &syn::Fields) -> syn::Result<proc_macro2::TokenStream> {
    match fields {
        syn::Fields::Named(_) => {
            let mut used_field_names = HashMap::new();
            let fields_tokens: Vec<_> = fields
                .iter()
                .map(|field| {
                    // Handle the 'rename' attribute.
                    let (field_name, field_span) = match find_rename_attribute(&field.attrs)? {
                        Some(name_and_span) => name_and_span,
                        None => (field.ident.clone().unwrap().to_string(), field.ident.span()), // safe since named fields.
                    };
                    check_for_name_collisions(&mut used_field_names, &field_name, field_span)?;

                    let field_schema_type = schema_type_field_type(field)?;
                    Ok(quote! {
                        (concordium_std::String::from(#field_name), #field_schema_type)
                    })
                })
                .collect::<syn::Result<_>>()?;
            Ok(
                quote! { concordium_std::schema::Fields::Named(concordium_std::Vec::from([ #(#fields_tokens),* ])) },
            )
        }
        syn::Fields::Unnamed(_) => {
            let fields_tokens: Vec<_> =
                fields.iter().map(schema_type_field_type).collect::<syn::Result<_>>()?;
            Ok(quote! { concordium_std::schema::Fields::Unnamed([ #(#fields_tokens),* ].to_vec()) })
        }
        syn::Fields::Unit => Ok(quote! { concordium_std::schema::Fields::None }),
    }
}

/// We reserve a number of error codes for custom errors, such as ParseError,
/// that are provided by concordium-std. These reserved error codes can have
/// indices i32::MIN, i32::MIN + 1, ..., RESERVED_ERROR_CODES
const RESERVED_ERROR_CODES: i32 = i32::MIN + 100;

/// Derive the conversion of enums that represent error types into the Reject
/// struct which can be used as the error type of init and receive functions.
/// Creating custom enums for error types can provide meaningful error messages
/// to the user of the smart contract.
///
/// When a contract function rejects, the enum is serialized and returned along
/// with the error code. The serialization means that the enum *must* implement
/// [`Serial`](../concordium_contracts_common/trait.Serial.html) if [`Reject`]
/// is to be derived.
///
/// The conversion will map the first variant to error code -1, second to -2,
/// etc.
///
/// ### Example
/// ```ignore
/// #[derive(Reject, Serial)]
/// enum MyError {
///     IllegalState, // receives error code -1
///     WrongSender, // receives error code -2
///     TimeExpired(time: Timestamp), // receives error code -3
///     ...
/// }
/// ```
/// ```ignore
/// #[receive(contract = "my_contract", name = "some_receive")]
/// fn receive<A: HasActions>(ctx: &impl HasReceiveContext, state: &mut MyState)
/// -> Result<A, MyError> {...}
/// ```
#[proc_macro_derive(Reject, attributes(from))]
pub fn reject_derive(input: TokenStream) -> TokenStream {
    unwrap_or_report(reject_derive_worker(input))
}

fn reject_derive_worker(input: TokenStream) -> syn::Result<TokenStream> {
    let ast: syn::DeriveInput = syn::parse(input)?;
    let enum_data = match &ast.data {
        syn::Data::Enum(data) => Ok(data),
        _ => Err(syn::Error::new(ast.span(), "Reject can only be derived for enums.")),
    }?;
    let enum_ident = &ast.ident;

    // Ensure that the number of enum variants fits into the number of error codes
    // we can generate.
    let too_many_variants = format!(
        "Error enum {} cannot have more than {} variants.",
        enum_ident,
        RESERVED_ERROR_CODES.neg()
    );
    match i32::try_from(enum_data.variants.len()) {
        Ok(n) if n <= RESERVED_ERROR_CODES.neg() => (),
        _ => {
            return Err(syn::Error::new(ast.span(), &too_many_variants));
        }
    };

    let variant_error_conversions = generate_variant_error_conversions(enum_data, enum_ident)?;
    let buf_var_ident = format_ident!("{}", "buf");
    let variant_matches = generate_variant_matches(enum_data, enum_ident, &buf_var_ident);

    let gen = quote! {
        /// The from implementation maps the first variant to -1, second to -2, etc.
        /// NB: This differs from the cast `variant as i32` since we cannot easily modify
        /// the variant tags in the derive macro itself.
        #[automatically_derived]
        impl From<#enum_ident> for Reject {
            #[inline(always)]
            fn from(e: #enum_ident) -> Self {
                let mut #buf_var_ident = Vec::new();
                concordium_std::Serial::serial(&e, &mut #buf_var_ident).unwrap_abort();
                match &e {
                   #variant_matches
                }
            }
        }

        #(#variant_error_conversions)*
    };
    Ok(gen.into())
}

/// Generate the cases for matching on the enum.
/// The error codes for variants start at -1 and go downwards.
/// The whole enum is serialized and included in the return_value field, which,
/// thus, is always `Some`.
fn generate_variant_matches(
    enum_data: &DataEnum,
    enum_name: &syn::Ident,
    buf_var_ident: &syn::Ident,
) -> proc_macro2::TokenStream {
    let mut match_cases = proc_macro2::TokenStream::new();
    for (index, variant) in enum_data.variants.iter().enumerate() {
        let variant_ident = &variant.ident;
        match variant.fields {
            syn::Fields::Named(_) => {
                match_cases.extend(quote! {
                    #enum_name::#variant_ident{..} => Reject {
                        error_code: unsafe { num::NonZeroI32::new_unchecked(-(#index as i32) - 1) },
                        return_value: Some(#buf_var_ident),
                    },
                });
            }
            syn::Fields::Unnamed(_) => {
                match_cases.extend(quote! {
                    #enum_name::#variant_ident(..) => Reject {
                        error_code: unsafe { num::NonZeroI32::new_unchecked(-(#index as i32) - 1) },
                        return_value: Some(#buf_var_ident),
                    },
                });
            }
            syn::Fields::Unit => {
                match_cases.extend(quote! {
                    #enum_name::#variant_ident => Reject {
                        error_code: unsafe { num::NonZeroI32::new_unchecked(-(#index as i32) - 1) },
                        return_value: Some(#buf_var_ident),
                    },
                });
            }
        };
    }
    match_cases
}

/// Generate error conversions for enum variants e.g. for converting
/// `ParseError` to `MyParseErrorWrapper` in
///
/// ```ignore
/// enum MyErrorType {
///   #[from(ParseError)]
///   MyParseErrorWrapper,
///   ...
/// }
/// ```
fn generate_variant_error_conversions(
    enum_data: &DataEnum,
    enum_name: &syn::Ident,
) -> syn::Result<Vec<proc_macro2::TokenStream>> {
    Ok(enum_data
        .variants
        .iter()
        .map(|variant| {
            // in the future we might incorporate explicit discriminants,
            // but the general case of this requires evaluating constant expressions,
            // which is not easily supported at the moment.
            if let Some((_, discriminant)) = variant.discriminant.as_ref() {
                return Err(syn::Error::new(
                    discriminant.span(),
                    "Explicit discriminants are not yet supported.",
                ));
            }
            let variant_attributes = variant.attrs.iter();
            variant_attributes
                .map(move |attr| {
                    parse_attr_and_gen_error_conversions(attr, enum_name, &variant.ident)
                })
                .collect::<syn::Result<Vec<_>>>()
        })
        .collect::<syn::Result<Vec<_>>>()?
        .into_iter()
        .flatten()
        .flatten()
        .collect())
}

/// Generate error conversion for a given enum variant.
fn parse_attr_and_gen_error_conversions(
    attr: &syn::Attribute,
    enum_name: &syn::Ident,
    variant_name: &syn::Ident,
) -> syn::Result<Vec<proc_macro2::TokenStream>> {
    let wrong_from_usage = |x: &dyn Spanned| {
        syn::Error::new(
            x.span(),
            "The `from` attribute expects a list of error types, e.g.: #[from(ParseError)].",
        )
    };
    match attr.parse_meta() {
        Ok(syn::Meta::List(list)) if list.path.is_ident("from") => {
            let mut from_error_names = vec![];
            for nested in list.nested.iter() {
                // check that all items in the list are paths
                match nested {
                    syn::NestedMeta::Meta(meta) => match meta {
                        Meta::Path(from_error) => {
                            from_error_names.push(from_error);
                        }
                        other => return Err(wrong_from_usage(&other)),
                    },
                    syn::NestedMeta::Lit(l) => return Err(wrong_from_usage(&l)),
                }
            }
            Ok(from_error_token_stream(&from_error_names, enum_name, variant_name).collect())
        }
        Ok(syn::Meta::NameValue(mnv)) if mnv.path.is_ident("from") => Err(wrong_from_usage(&mnv)),
        _ => Ok(vec![]),
    }
}

/// Generating the conversion code a la
/// ```ignore
/// impl From<ParseError> for MyErrorType {
///    fn from(x: ParseError) -> Self {
///      MyError::MyParseErrorWrapper
///    }
/// }
/// ```
fn from_error_token_stream<'a>(
    paths: &'a [&'a syn::Path],
    enum_name: &'a syn::Ident,
    variant_name: &'a syn::Ident,
) -> impl Iterator<Item = proc_macro2::TokenStream> + 'a {
    paths.iter().map(move |from_error| {
        quote! {
        impl From<#from_error> for #enum_name {
           #[inline]
           fn from(fe: #from_error) -> Self {
             #enum_name::#variant_name
           }
        }}
    })
}

#[proc_macro_attribute]
/// Derive the appropriate export for an annotated test function, when feature
/// "wasm-test" is enabled, otherwise behaves like `#[test]`.
pub fn concordium_test(attr: TokenStream, item: TokenStream) -> TokenStream {
    unwrap_or_report(concordium_test_worker(attr, item))
}

/// Derive the appropriate export for an annotated test function, when feature
/// "wasm-test" is enabled, otherwise behaves like `#[test]`.
#[cfg(feature = "wasm-test")]
fn concordium_test_worker(_attr: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
    let test_fn_ast: syn::ItemFn =
        attach_error(syn::parse(item), "#[concordium_test] can only be applied to functions.")?;

    let test_fn_name = &test_fn_ast.sig.ident;
    let rust_export_fn_name = format_ident!("concordium_test_{}", test_fn_name);
    let wasm_export_fn_name = format!("concordium_test {}", test_fn_name);

    let test_fn = quote! {
        // Setup test function
        #test_fn_ast

        // Export test function in wasm
        #[export_name = #wasm_export_fn_name]
        pub extern "C" fn #rust_export_fn_name() {
            #test_fn_name()
        }
    };
    Ok(test_fn.into())
}

/// Derive the appropriate export for an annotated test function, when feature
/// "wasm-test" is enabled, otherwise behaves like `#[test]`.
#[cfg(not(feature = "wasm-test"))]
fn concordium_test_worker(_attr: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
    let test_fn_ast: syn::ItemFn =
        attach_error(syn::parse(item), "#[concordium_test] can only be applied to functions.")?;

    let test_fn = quote! {
        #[test]
        #test_fn_ast
    };
    Ok(test_fn.into())
}

/// Sets the cfg for testing targeting either Wasm and native.
#[cfg(feature = "wasm-test")]
#[proc_macro_attribute]
pub fn concordium_cfg_test(_attr: TokenStream, item: TokenStream) -> TokenStream { item }

/// Sets the cfg for testing targeting either Wasm and native.
#[cfg(not(feature = "wasm-test"))]
#[proc_macro_attribute]
pub fn concordium_cfg_test(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item = proc_macro2::TokenStream::from(item);
    let out = quote! {
        #[cfg(test)]
        #item
    };
    out.into()
}

/// Derive the Deletable trait.
/// See the documentation of
/// [`derive(Deletable)`](./derive.Deletable.html) for details and limitations.
///
/// The trait should be derived for types which have not implemented the
/// `Serialize` trait. That is, Deletable should be derived for types with a
/// non-trivial state.
/// Non-trivial state here means when you have a type `MyState` which has one or
/// more fields comprised of
/// [`StateBox`](../concordium_std/struct.StateBox.html),
/// [`StateSet`](../concordium_std/struct.StateSet.html), or
/// [`StateMap`](../concordium_std/struct.StateMap.html).
///
/// Please note that it is
/// necessary to specify the generic parameter name for the
/// [`HasStateApi`](../concordium_std/trait.HasStateApi.html) generic parameter.
/// To do so, use the `#[concordium(state_parameter =
/// "NameOfGenericParameter")]` attribute on the type you are deriving
/// `Deletable` for.
///
/// # Example
/// ``` ignore
/// #[derive(Serial, DeserialWithState, Deletable)]
/// #[concordium(state_parameter = "S")]
/// struct MyState<S> {
///    my_state_map: StateMap<SomeType, SomeOtherType, S>,
/// }
/// ```
#[proc_macro_derive(Deletable, attributes(concordium))]
pub fn deletable_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input);
    unwrap_or_report(impl_deletable(&ast))
}

fn impl_deletable_field(ident: &proc_macro2::TokenStream) -> syn::Result<proc_macro2::TokenStream> {
    Ok(quote!({
        #ident.delete();
    }))
}

fn impl_deletable(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let data_name = &ast.ident;
    let state_parameter = match find_state_parameter_attribute(&ast.attrs)? {
        Some(state_param) => state_param,
        None => {
            return Err(syn::Error::new(
                Span::call_site(),
                "Deletable requires the attribute #[concordium(state_parameter = \"S\")], where \
                 \"S\" should be the HasStateApi generic parameter.",
            ))
        }
    };

    let (impl_generics, ty_generics, where_clauses) = ast.generics.split_for_impl();
    let where_predicates = where_clauses.map(|c| c.predicates.clone());
    let body = match ast.data {
        syn::Data::Struct(ref data) => {
            let fields_tokens = match data.fields {
                syn::Fields::Named(_) => {
                    data.fields
                        .iter()
                        .map(|field| {
                            let field_ident = field.ident.clone().unwrap(); // safe since named fields.
                            let field_ident = quote!(self.#field_ident);
                            impl_deletable_field(&field_ident)
                        })
                        .collect::<syn::Result<_>>()?
                }
                syn::Fields::Unnamed(_) => data
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, _)| {
                        let i = syn::LitInt::new(i.to_string().as_str(), Span::call_site());
                        let field_ident = quote!(self.#i);
                        impl_deletable_field(&field_ident)
                    })
                    .collect::<syn::Result<_>>()?,
                syn::Fields::Unit => proc_macro2::TokenStream::new(),
            };
            quote! {
                #fields_tokens
            }
        }
        syn::Data::Enum(ref data) => {
            let mut matches_tokens = proc_macro2::TokenStream::new();
            for (_, variant) in data.variants.iter().enumerate() {
                let (field_names, pattern) = match variant.fields {
                    syn::Fields::Named(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .map(|field| field.ident.clone().unwrap())
                            .collect();
                        (field_names.clone(), quote! { {#(#field_names),*} })
                    }
                    syn::Fields::Unnamed(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, _)| format_ident!("x_{}", i))
                            .collect();
                        (field_names.clone(), quote! { (#(#field_names),*) })
                    }
                    syn::Fields::Unit => (Vec::new(), proc_macro2::TokenStream::new()),
                };
                let field_tokens: proc_macro2::TokenStream = field_names
                    .iter()
                    .zip(variant.fields.iter())
                    .map(|(name, _)| impl_deletable_field(&quote!(#name)))
                    .collect::<syn::Result<_>>()?;
                let variant_ident = &variant.ident;

                matches_tokens.extend(quote! {
                    #data_name::#variant_ident#pattern => {
                        #field_tokens
                    },
                })
            }
            quote! {
                match self {
                    #matches_tokens
                }
            }
        }
        _ => unimplemented!("#[derive(Deletable)] is not implemented for union."),
    };

    let gen = quote! {
        #[automatically_derived]
        impl #impl_generics Deletable for #data_name #ty_generics where #state_parameter : HasStateApi, #where_predicates {
            fn delete(self) {
                use concordium_std::Deletable;
                #body
            }
        }
    };

    Ok(gen.into())
}

/// If `wasm-test` feature of `concordium-std` is enabled ignore the item,
/// this usually happens when executing tests with `cargo-concordium` utility.
/// Otherwise this is equivalent to `#[cfg(not(test))]`. Use as a dual to
/// `#[concordium_cfg_test]`.
#[cfg(feature = "wasm-test")]
#[proc_macro_attribute]
pub fn concordium_cfg_not_test(_attr: TokenStream, _item: TokenStream) -> TokenStream {
    TokenStream::new()
}

/// If `wasm-test` feature of `concordium-std` is enabled ignore the item,
/// this usually happens when executing tests with `cargo-concordium` utility.
/// Otherwise this is equivalent to `#[cfg(not(test))]`. Use as a dual to
/// `#[concordium_cfg_test]`.
#[cfg(not(feature = "wasm-test"))]
#[proc_macro_attribute]
pub fn concordium_cfg_not_test(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item = proc_macro2::TokenStream::from(item);
    let out = quote! {
        #[cfg(not(test))]
        #item
    };
    out.into()
}

/// Derive the StateClone trait.
/// See the documentation of
/// [`derive(StateClone)`](./derive.StateClone.html) for details and
/// limitations.
///
/// The trait is used in the
/// [`TestHost`](../concordium_std/test_infrastructure/struct.TestHost.html)
/// when rolling back the state. If that functionality is needed, then this
/// trait must be derived for types which have not implement the `Clone` trait.
/// That is, `StateClone` should be derived for types with a non-trivial state.
/// Non-trivial state here means when you have a type `MyState` which has one or
/// more fields comprised of
/// [`StateBox`](../concordium_std/struct.StateBox.html),
/// [`StateSet`](../concordium_std/struct.StateSet.html), or
/// [`StateMap`](../concordium_std/struct.StateMap.html).
///
/// Please note that it is
/// necessary to specify the generic parameter name for the
/// [`HasStateApi`](../concordium_std/trait.HasStateApi.html) generic parameter.
/// To do so, use the `#[concordium(state_parameter =
/// "NameOfGenericParameter")]` attribute on the type you are deriving
/// `StateClone` for.
///
/// # Example
/// ``` ignore
/// #[derive(Serial, DeserialWithState, StateClone)]
/// #[concordium(state_parameter = "S")]
/// struct MyState<S> {
///    my_state_map: StateMap<SomeType, SomeOtherType, S>,
/// }
/// ```
#[proc_macro_derive(StateClone, attributes(concordium))]
pub fn state_clone_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input);
    unwrap_or_report(impl_state_clone(&ast))
}

fn impl_state_clone(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let data_name = &ast.ident;
    let state_parameter = match find_state_parameter_attribute(&ast.attrs)? {
        Some(state_param) => state_param,
        None => {
            return Err(syn::Error::new(
                Span::call_site(),
                "StateClone requires the attribute #[concordium(state_parameter = \"S\")], where \
                 \"S\" should be the HasStateApi generic parameter.",
            ))
        }
    };

    let (impl_generics, ty_generics, where_clauses) = ast.generics.split_for_impl();
    let where_predicates = where_clauses.map(|c| c.predicates.clone());
    let body_tokens = match ast.data {
        syn::Data::Struct(ref data) => {
            let mut field_names = proc_macro2::TokenStream::new();
            let mut field_tokens = proc_macro2::TokenStream::new();
            let return_tokens = match data.fields {
                syn::Fields::Named(_) => {
                    for field in data.fields.iter() {
                        let field_ident = field.ident.clone().unwrap(); // safe since named fields.
                        field_tokens.extend(quote!(let #field_ident = concordium_std::StateClone::clone_state(&self.#field_ident, cloned_state_api);));
                        field_names.extend(quote!(#field_ident,));
                    }
                    quote!(Self{#field_names})
                }
                syn::Fields::Unnamed(_) => {
                    for i in 0..data.fields.len() {
                        let field_index = syn::Index::from(i);
                        let variable_ident = format_ident!("x_{}", i);
                        field_tokens
                            .extend(quote!(let #variable_ident = concordium_std::StateClone::clone_state(&self.#field_index, cloned_state_api);));
                        field_names.extend(quote!(#variable_ident,))
                    }
                    quote!(Self(#field_names))
                }
                syn::Fields::Unit => quote!(Ok(Self {})),
            };
            quote! {
                #field_tokens
                #return_tokens
            }
        }
        syn::Data::Enum(ref data) => {
            let mut matches_tokens = proc_macro2::TokenStream::new();
            for (_, variant) in data.variants.iter().enumerate() {
                let mut field_names = proc_macro2::TokenStream::new();
                let mut field_tokens = proc_macro2::TokenStream::new();
                let variant_ident = &variant.ident;

                let (return_tokens, pattern) = match variant.fields {
                    syn::Fields::Named(_) => {
                        for field in variant.fields.iter() {
                            let field_ident = field.ident.clone().unwrap(); // safe since named fields.
                            field_tokens.extend(quote!(let #field_ident = concordium_std::StateClone::clone_state(#field_ident, cloned_state_api);));
                            field_names.extend(quote!(#field_ident,));
                        }
                        let pattern = quote!({#field_names});
                        (quote!(#data_name::#variant_ident#pattern), pattern)
                    }
                    syn::Fields::Unnamed(_) => {
                        for i in 0..variant.fields.len() {
                            let field_ident = format_ident!("x_{}", i);
                            field_tokens.extend(quote!(let #field_ident = concordium_std::StateClone::clone_state(#field_ident, cloned_state_api);));
                            field_names.extend(quote!(#field_ident,));
                        }
                        let pattern = quote!((#field_names));
                        (quote!(#data_name::#variant_ident#pattern), pattern)
                    }
                    syn::Fields::Unit => (
                        quote!(#data_name::#variant_ident#field_names),
                        proc_macro2::TokenStream::new(),
                    ),
                };
                let variant_ident = &variant.ident;

                matches_tokens.extend(quote! {
                    #data_name::#variant_ident#pattern => {
                        #field_tokens
                        #return_tokens
                    },
                })
            }
            quote! {
                match self {
                    #matches_tokens
                }
            }
        }
        _ => unimplemented!("#[derive(StateClone)] is not implemented for union."),
    };

    let gen = quote! {
        #[automatically_derived]
        unsafe impl #impl_generics concordium_std::StateClone<#state_parameter> for #data_name #ty_generics where #state_parameter: concordium_std::HasStateApi, #where_predicates {
            unsafe fn clone_state(&self, cloned_state_api: &#state_parameter) -> Self {
                #body_tokens
            }
        }
    };

    Ok(gen.into())
}
