//! This library provides types and functions for working with the Concordium
//! Token Standard CTS1.
//!
//! It contains types for the parameters for each of the contract functions and
//! types for each event. Each type have implemented serialization according to
//! CTS1.
//!
//! # Example using `TransferParams`
//!
//! ```ignore
//! #[receive(contract = "MyTokenContract", name = "transfer", parameter = "TransferParams", enable_logger)]
//! fn contract_transfer<A: HasActions>(
//!     ctx: &impl HasReceiveContext,
//!     logger: &mut impl HasLogger,
//!     state: &mut State,
//! ) -> ContractResult<A> {
//!     // Parse the parameter.
//!     let TransferParams(transfers) = ctx.parameter_cursor().get()?;
//!     // ...
//!     Ok(A::accept())
//! }
#![cfg_attr(not(feature = "std"), no_std)]
use concordium_std::*;

/// Sha256 digest
pub type Sha256 = [u8; 32];

/// The location of the metadata and an optional hash of the content.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct MetadataUrl {
    /// The URL following the specification RFC1738.
    #[concordium(size_length = 2)]
    pub url:  String,
    /// A optional hash of the content.
    pub hash: Option<Sha256>,
}

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of a token type.
pub type TokenId = u64;

/// An amount of a specific token type.
pub type TokenAmount = u64;

/// An event of a transfer of some amount of tokens from one address to another.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct TransferEvent {
    /// The ID of the token being transferred.
    pub token_id: TokenId,
    /// The amount of tokens being transferred.
    pub amount:   TokenAmount,
    /// The address owning these tokens before the transfer.
    pub from:     Address,
    /// The address to receive these tokens after the transfer.
    pub to:       Address,
}

/// An event of an update to an operator address for an owner address.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct UpdateOperatorEvent {
    /// The update to the operator.
    pub update:   OperatorUpdate,
    /// The address for whom, the operator is updated.
    pub owner:    Address,
    /// The address who is the operator being updated.
    pub operator: Address,
}

/// An event of tokens being minted, could be a new token type or extending the
/// total supply of existing token.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct MintEvent {
    /// The ID of the token being minted, (possibly a new token ID).
    pub token_id: TokenId,
    /// The number of tokens being minted, this is allowed to be 0 as well.
    pub amount:   TokenAmount,
    /// The initial owner of these newly minted amount of tokens.
    pub owner:    Address,
}

/// An event of some amount of a token type being burned.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct BurnEvent {
    /// The ID of the token where an amount is being burned.
    pub token_id: TokenId,
    /// The amount of tokens being burned.
    pub amount:   TokenAmount,
    /// The owner of the tokens being burned.
    pub owner:    Address,
}

/// An event for setting the metadata for a token.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct TokenMetadataEvent {
    /// The ID of the token.
    pub token_id:     TokenId,
    /// The location of the metadata.
    pub metadata_url: MetadataUrl,
}

/// Event to be printed in the log.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of these events and the order of their fields
// cannot be changed. However new custom events can safely be appended.
#[derive(Serialize, SchemaType)]
pub enum Event {
    /// A transfer between two addresses of some amount of tokens.
    Transfer(TransferEvent),
    /// Updates to an operator for a specific address and token id.
    UpdateOperator(UpdateOperatorEvent),
    /// Creation of new tokens, could be both adding some amounts to an existing
    /// token or a entirely new token.
    Mint(MintEvent),
    /// Destruction of tokens removing some amounts of a token.
    Burn(BurnEvent),
    /// Setting the metadata for a token.
    TokenMetadata(TokenMetadataEvent),
    /// Custom event not specified by CTS1.
    Custom(#[concordium(size_length = 2)] Vec<u8>),
}

/// The different errors the contract can produce.
#[derive(Debug, PartialEq, Eq)]
pub enum Cts1Error<R> {
    /// Invalid token id
    InvalidTokenId,
    /// The balance of the token owner is insufficient for the transfer.
    InsufficientFunds,
    /// Sender is neither the token owner or an operator of the owner for this
    /// token.
    Unauthorized,
    /// Make the sender an operator of the sender is invalid.
    OperatorIsSender,
    /// Only contracts can send to this function.
    ContractOnly,
    /// Custom error
    Custom(R),
}

impl<R: Into<Reject>> From<Cts1Error<R>> for Reject {
    fn from(err: Cts1Error<R>) -> Self {
        let error_code = match err {
            Cts1Error::InvalidTokenId => unsafe {
                crate::num::NonZeroI32::new_unchecked(-42000001)
            },
            Cts1Error::InsufficientFunds => unsafe {
                crate::num::NonZeroI32::new_unchecked(-42000002)
            },
            Cts1Error::Unauthorized => unsafe { crate::num::NonZeroI32::new_unchecked(-42000003) },
            Cts1Error::OperatorIsSender => unsafe {
                crate::num::NonZeroI32::new_unchecked(-42000004)
            },
            Cts1Error::ContractOnly => unsafe { crate::num::NonZeroI32::new_unchecked(-42000005) },
            Cts1Error::Custom(reject) => reject.into().error_code,
        };
        Self {
            error_code,
        }
    }
}

impl<X: From<LogError>> From<LogError> for Cts1Error<X> {
    fn from(err: LogError) -> Self { Cts1Error::Custom(X::from(err)) }
}

impl<X: From<ParseError>> From<ParseError> for Cts1Error<X> {
    fn from(err: ParseError) -> Self { Cts1Error::Custom(X::from(err)) }
}

/// The receiving address for a transfer, similar to the Address type, but
/// contains extra information when the receiver address is a contract.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the variants and the order of their fields
// cannot be changed.
#[derive(Serialize, SchemaType)]
pub enum Receiver {
    /// The receiver is an account address.
    Account(AccountAddress),
    /// The receiver is a contract address.
    Contract {
        /// The receiving address.
        address:  ContractAddress,
        /// The function to call on the receiving contract.
        function: OwnedReceiveName,
        /// Some additional bytes to send with the function.
        #[concordium(size_length = 2)]
        data:     Vec<u8>,
    },
}

impl Receiver {
    /// Get the Address of the receiver.
    pub fn address(&self) -> Address {
        match self {
            Receiver::Account(address) => Address::Account(*address),
            Receiver::Contract {
                address,
                ..
            } => Address::Contract(*address),
        }
    }
}

/// A single transfer of some amount of a token.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct Transfer {
    /// The ID of the token being transferred.
    pub token_id: TokenId,
    /// The amount of tokens being transferred.
    pub amount:   TokenAmount,
    /// The address owning the tokens being transferred.
    pub from:     Address,
    /// The address receiving the tokens being transferred.
    pub to:       Receiver,
}

/// The parameter type for the contract function `transfer`.
#[derive(Serialize, SchemaType)]
pub struct TransferParams(#[concordium(size_length = 1)] pub Vec<Transfer>);

/// The update to an the operator.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the variants cannot be changed.
#[derive(Serialize, SchemaType)]
pub enum OperatorUpdate {
    /// Remove the operator.
    Remove,
    /// Add an address as an operator.
    Add,
}

/// The parameter type for the contract function `updateOperator`.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct UpdateOperatorParams {
    /// The update for this operator.
    pub update:   OperatorUpdate,
    /// The address which is either added or removed as an operator.
    /// Note: The address for whom this will become an operator is the sender of
    /// the contract transaction.
    pub operator: Address,
}

/// A query for the balance of a given address for a given token.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct BalanceOfQuery {
    /// The ID of the token for which to query the balance of.
    pub token_id: TokenId,
    /// The address for which to query the balance of.
    pub address:  Address,
}

/// The parameter type for the contract function `balanceOf`.
/// This is contract function can only be called by another contract instance,
/// and there is no reason to derive a SchemaType for this example.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct BalanceOfQueryParams {
    /// The contract function to trigger with the results of the queries.
    pub callback: OwnedReceiveName,
    /// List of balance queries.
    #[concordium(size_length = 1)]
    pub queries:  Vec<BalanceOfQuery>,
}

/// The response which is sent back when calling the contract function
/// `balanceOf`.
/// It consists of the list of queries paired with their corresponding result.
#[derive(Serialize, SchemaType)]
pub struct BalanceOfQueryResponse(
    #[concordium(size_length = 1)] pub Vec<(BalanceOfQuery, TokenAmount)>,
);

/// The parameter type for a contract function which receives CTS1 tokens.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Serialize, SchemaType)]
pub struct OnReceivingCTS1Params {
    /// The ID of the token received.
    pub token_id:      TokenId,
    /// The amount of tokens received.
    pub amount:        TokenAmount,
    /// The previous owner of the tokens.
    pub from:          Address,
    /// The name of the token contract which is tracking the token and
    /// implements CTS1.
    pub contract_name: OwnedContractName,
    /// Some extra information which where sent as part of the transfer.
    #[concordium(size_length = 2)]
    pub data:          Vec<u8>,
}
