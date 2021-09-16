//! This library provides types and functions for working with the Concordium
//! Token Standard CTS1.
//!
//! It contains types for the parameters for each of the contract functions and
//! types for each event. Each type have implemented serialization according to
//! CTS1.
//! Additionally the crate exports an CTS1Error wrapper type which can be used
//! to wrap and extend a custom error type. This will ensure the CTS1 errors
//! have the correct error codes.
//!
//! # Example using `TransferParams`
//!
//! ```ignore
//! type TransferParameter = TransferParams<TokenIdVec>;
//!
//! #[receive(contract = "MyTokenContract", name = "transfer", parameter = "TransferParameter", enable_logger)]
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
#[cfg(not(feature = "std"))]
use core::fmt;
#[cfg(feature = "std")]
use std::fmt;

use convert::TryFrom;

/// Sha256 digest
pub type Sha256 = [u8; 32];

/// The location of the metadata and an optional hash of the content.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct MetadataUrl {
    /// The URL following the specification RFC1738.
    #[concordium(size_length = 2)]
    pub url:  String,
    /// A optional hash of the content.
    pub hash: Option<Sha256>,
}

/// Trait for marking types as CTS1 token IDs.
/// For a type to be a valid CTS1 token ID it must implement serialization and
/// schema type, such that the first byte indicates how many bytes is used to
/// represent the token ID, followed by this many bytes for the token ID.
///
/// Note: The reason for introducing such a trait instead of representing every
/// token ID using Vec<u8> is to allow smart contracts to use specialized token
/// ID implementations avoiding allocations.
pub trait IsTokenId: Serialize + schema::SchemaType {}

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of a token type.
///
/// This token ID type can represent every possible token ID but requires
/// allocating a Vec. Using a fixed size token ID type (such as `TokenIdFixed`)
/// will avoid this.
///
/// The CTS1 specification allows for up to 255 bytes for the token ID, but
/// unless the bytes have some significant meaning, it is most likely better to
/// use a smaller fixed size token ID such as `TokenIdU8`.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Clone, Serialize)]
pub struct TokenIdVec(#[concordium(size_length = 1)] pub Vec<u8>);

impl IsTokenId for TokenIdVec {}

impl schema::SchemaType for TokenIdVec {
    fn get_type() -> schema::Type {
        schema::Type::List(schema::SizeLength::U8, Box::new(schema::Type::U8))
    }
}

/// Display the token ID as a uppercase hex string
impl fmt::Display for TokenIdVec {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for byte in &self.0 {
            write!(f, "{:02X}", byte)?;
        }
        Ok(())
    }
}

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of a token type.
///
/// The CTS1 specification allows for up to 255 bytes for the token ID, but for
/// most cases using a smaller token ID is fine and can reduce contract energy
/// costs.
///
/// This token ID uses an array for representing the token ID bytes which means
/// the token ID space is fixed to `N` number of bytes and some token IDs cannot
/// be represented. For a more general token ID type see `TokenIdVec`.
/// For fixed sized token IDs with integer representations see `TokenIdU8`,
/// `TokenIdU16`, `TokenIdU32` and `TokenIdU64`.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Copy, Clone)]
pub struct TokenIdFixed<const N: usize>(pub [u8; N]);

impl<const N: usize> IsTokenId for TokenIdFixed<N> {}

impl<const N: usize> schema::SchemaType for TokenIdFixed<N> {
    fn get_type() -> schema::Type {
        schema::Type::List(schema::SizeLength::U8, Box::new(schema::Type::U8))
    }
}

impl<const N: usize> From<[u8; N]> for TokenIdFixed<N> {
    fn from(id: [u8; N]) -> Self { TokenIdFixed(id) }
}

/// The `TokenIdFixed` is serialized as the value of the first byte represents
/// the number of bytes followed for the rest of the token ID.
impl<const N: usize> Serial for TokenIdFixed<N> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        let len = u8::try_from(N).map_err(|_| W::Err::default())?;
        out.write_u8(len)?;
        for byte in self.0 {
            out.write_u8(byte)?;
        }
        Ok(())
    }
}

/// The `TokenIdFixed` is deserialized by reading the first byte represents the
/// number of bytes and ensuring this value corresponds with the number of bytes
/// to use for the token ID.
impl<const N: usize> Deserial for TokenIdFixed<N> {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let byte_length = source.read_u8()?;
        if usize::from(byte_length) != N {
            return Err(ParseError::default());
        }
        let bytes: [u8; N] = source.get()?;
        Ok(TokenIdFixed(bytes))
    }
}

/// Display the token ID as a uppercase hex string
impl<const N: usize> fmt::Display for TokenIdFixed<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for byte in &self.0 {
            write!(f, "{:02X}", byte)?;
        }
        Ok(())
    }
}

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of a token type.
///
/// The CTS1 specification allows for up to 255 bytes for the token ID, but for
/// most cases using a smaller token ID is fine and can reduce contract energy
/// costs.
///
/// This token ID uses u64 for representing the token ID bytes which means the
/// token ID space is fixed to 8 bytes and some token IDs cannot be represented.
/// For a more general token ID type see `TokenIdVec`.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Copy, Clone)]
pub struct TokenIdU64(pub u64);

impl IsTokenId for TokenIdU64 {}

impl schema::SchemaType for TokenIdU64 {
    fn get_type() -> schema::Type {
        schema::Type::List(schema::SizeLength::U8, Box::new(schema::Type::U8))
    }
}

impl From<u64> for TokenIdU64 {
    fn from(id: u64) -> Self { TokenIdU64(id) }
}

/// The `TokenIdU64` is serialized with one byte with the value 8 followed by 8
/// bytes to encode a u64 in little endian.
impl Serial for TokenIdU64 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_u8(8)?;
        out.write_u64(self.0)
    }
}

/// The `TokenIdU64` will deserialize one byte ensuring this contains the value
/// 8 and then deserialize a u64 as little endian. It will result in an error if
/// the first byte is not 8.
impl Deserial for TokenIdU64 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let byte_length = source.read_u8()?;
        if byte_length == 8 {
            Ok(TokenIdU64(source.read_u64()?))
        } else {
            Err(ParseError::default())
        }
    }
}

/// Display the token ID as a uppercase hex string
impl fmt::Display for TokenIdU64 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for byte in &self.0.to_le_bytes() {
            write!(f, "{:02X}", byte)?;
        }
        Ok(())
    }
}

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of a token type.
///
/// The CTS1 specification allows for up to 255 bytes for the token ID, but for
/// most cases using a smaller token ID is fine and can reduce contract energy
/// costs.
///
/// This token ID uses u32 for representing the token ID bytes which means the
/// token ID space is fixed to 4 bytes and some token IDs cannot be represented.
/// For a more general token ID type see `TokenIdVec`.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Copy, Clone)]
pub struct TokenIdU32(pub u32);

impl IsTokenId for TokenIdU32 {}

impl schema::SchemaType for TokenIdU32 {
    fn get_type() -> schema::Type {
        schema::Type::List(schema::SizeLength::U8, Box::new(schema::Type::U8))
    }
}

impl From<u32> for TokenIdU32 {
    fn from(id: u32) -> Self { TokenIdU32(id) }
}

/// The `TokenIdU32` is serialized with one byte with the value 4 followed by 4
/// bytes to encode a u32 in little endian.
impl Serial for TokenIdU32 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_u8(4)?;
        out.write_u32(self.0)
    }
}

/// The `TokenIdU32` will deserialize one byte ensuring this contains the value
/// 4 and then deserialize a u32 as little endian. It will result in an error if
/// the first byte is not 4.
impl Deserial for TokenIdU32 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let byte_length = source.read_u8()?;
        if byte_length == 4 {
            Ok(TokenIdU32(source.read_u32()?))
        } else {
            Err(ParseError::default())
        }
    }
}

/// Display the token ID as a uppercase hex string
impl fmt::Display for TokenIdU32 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for byte in &self.0.to_le_bytes() {
            write!(f, "{:02X}", byte)?;
        }
        Ok(())
    }
}

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of a token type.
///
/// The CTS1 specification allows for up to 255 bytes for the token ID, but for
/// most cases using a smaller token ID is fine and can reduce contract energy
/// costs.
///
/// This token ID uses u16 for representing the token ID bytes which means the
/// token ID space is fixed to 2 bytes and some token IDs cannot be represented.
/// For a more general token ID type see `TokenIdVec`.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Copy, Clone)]
pub struct TokenIdU16(pub u16);

impl IsTokenId for TokenIdU16 {}

impl schema::SchemaType for TokenIdU16 {
    fn get_type() -> schema::Type {
        schema::Type::List(schema::SizeLength::U8, Box::new(schema::Type::U8))
    }
}

impl From<u16> for TokenIdU16 {
    fn from(id: u16) -> Self { TokenIdU16(id) }
}

/// The `TokenIdU16` is serialized with one byte with the value 2 followed by 2
/// bytes to encode a u16 in little endian.
impl Serial for TokenIdU16 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_u8(2)?;
        out.write_u16(self.0)
    }
}

/// The `TokenIdU16` will deserialize one byte ensuring this contains the value
/// 2 and then deserialize a u16 as little endian. It will result in an error if
/// the first byte is not 2.
impl Deserial for TokenIdU16 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let byte_length = source.read_u8()?;
        if byte_length == 2 {
            Ok(TokenIdU16(source.read_u16()?))
        } else {
            Err(ParseError::default())
        }
    }
}

/// Display the token ID as a uppercase hex string
impl fmt::Display for TokenIdU16 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for byte in &self.0.to_le_bytes() {
            write!(f, "{:02X}", byte)?;
        }
        Ok(())
    }
}

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of a token type.
///
/// The CTS1 specification allows for up to 255 bytes for the token ID, but for
/// most cases using a smaller token ID is fine and can reduce contract energy
/// costs.
///
/// This token ID uses u8 for representing the token ID bytes which means the
/// token ID space is fixed to 1 byte and some token IDs cannot be represented.
/// For a more general token ID type see `TokenIdVec`.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Copy, Clone)]
pub struct TokenIdU8(pub u8);

impl IsTokenId for TokenIdU8 {}

impl schema::SchemaType for TokenIdU8 {
    fn get_type() -> schema::Type {
        schema::Type::List(schema::SizeLength::U8, Box::new(schema::Type::U8))
    }
}

impl From<u8> for TokenIdU8 {
    fn from(id: u8) -> Self { TokenIdU8(id) }
}

/// The `TokenIdU8` is serialized with one byte with the value 1 followed by 1
/// bytes to encode a u8 in little endian.
impl Serial for TokenIdU8 {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_u8(1)?;
        out.write_u8(self.0)
    }
}

/// The `TokenIdU8` will deserialize one byte ensuring this contains the value 1
/// and then deserialize a u8 as little endian. It will result in an error if
/// the first byte is not 1.
impl Deserial for TokenIdU8 {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let byte_length = source.read_u8()?;
        if byte_length == 1 {
            Ok(TokenIdU8(source.read_u8()?))
        } else {
            Err(ParseError::default())
        }
    }
}

/// Display the token ID as a uppercase hex string
impl fmt::Display for TokenIdU8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for byte in &self.0.to_le_bytes() {
            write!(f, "{:02X}", byte)?;
        }
        Ok(())
    }
}

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of a token type.
///
/// The CTS1 specification allows for up to 255 bytes for the token ID, but for
/// most cases using a smaller token ID is fine and can reduce contract energy
/// costs.
///
/// This token ID uses Unit for representing token IDs, which means only one
/// token ID can be represented with this type and other token IDs cannot be
/// represented. For a more general token ID type see `TokenIdVec`.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Copy, Clone)]
pub struct TokenIdUnit();

impl IsTokenId for TokenIdUnit {}

impl schema::SchemaType for TokenIdUnit {
    fn get_type() -> schema::Type {
        schema::Type::List(schema::SizeLength::U8, Box::new(schema::Type::U8))
    }
}

/// The `TokenIdUnit` is serialized with one byte with the value 0.
impl Serial for TokenIdUnit {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_u8(0)?;
        Ok(())
    }
}

/// The `TokenIdUnit` will deserialize one byte ensuring this contains the value
/// 0. It will result in an error if the byte is not 0.
impl Deserial for TokenIdUnit {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let byte_length = source.read_u8()?;
        if byte_length == 0 {
            Ok(TokenIdUnit())
        } else {
            Err(ParseError::default())
        }
    }
}

/// An amount of a specific token type.
pub type TokenAmount = u64;

/// An event of a transfer of some amount of tokens from one address to another.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct TransferEvent<T: IsTokenId> {
    /// The ID of the token being transferred.
    pub token_id: T,
    /// The amount of tokens being transferred.
    pub amount:   TokenAmount,
    /// The address owning these tokens before the transfer.
    pub from:     Address,
    /// The address to receive these tokens after the transfer.
    pub to:       Address,
}

/// An event of tokens being minted, could be a new token type or extending the
/// total supply of existing token.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct MintEvent<T: IsTokenId> {
    /// The ID of the token being minted, (possibly a new token ID).
    pub token_id: T,
    /// The number of tokens being minted, this is allowed to be 0 as well.
    pub amount:   TokenAmount,
    /// The initial owner of these newly minted amount of tokens.
    pub owner:    Address,
}

/// An event of some amount of a token type being burned.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct BurnEvent<T: IsTokenId> {
    /// The ID of the token where an amount is being burned.
    pub token_id: T,
    /// The amount of tokens being burned.
    pub amount:   TokenAmount,
    /// The owner of the tokens being burned.
    pub owner:    Address,
}

/// An event of an update to an operator address for an owner address.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct UpdateOperatorEvent {
    /// The update to the operator.
    pub update:   OperatorUpdate,
    /// The address for whom, the operator is updated.
    pub owner:    Address,
    /// The address who is the operator being updated.
    pub operator: Address,
}

/// An event for setting the metadata for a token.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct TokenMetadataEvent<T: IsTokenId> {
    /// The ID of the token.
    pub token_id:     T,
    /// The location of the metadata.
    pub metadata_url: MetadataUrl,
}

/// Event to be printed in the log.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of these events and the order of their fields
// cannot be changed. However new custom events can safely be appended.
#[derive(Debug, Serialize, SchemaType)]
pub enum Event<T: IsTokenId> {
    /// A transfer between two addresses of some amount of tokens.
    Transfer(TransferEvent<T>),
    /// Creation of new tokens, could be both adding some amounts to an existing
    /// token or introduce an entirely new token ID.
    Mint(MintEvent<T>),
    /// Destruction of tokens removing some amounts of a token.
    Burn(BurnEvent<T>),
    /// Updates to an operator for a specific address and token id.
    UpdateOperator(UpdateOperatorEvent),
    /// Setting the metadata for a token.
    TokenMetadata(TokenMetadataEvent<T>),
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
#[derive(Debug, Serialize, SchemaType)]
pub enum Receiver {
    /// The receiver is an account address.
    Account {
        /// The receiving address.
        address: AccountAddress,
    },
    /// The receiver is a contract address.
    Contract {
        /// The receiving address.
        address:  ContractAddress,
        /// The function to call on the receiving contract.
        function: OwnedReceiveName,
    },
}

impl Receiver {
    /// Construct a receiver from an account address.
    pub fn from_account(address: AccountAddress) -> Self {
        Receiver::Account {
            address,
        }
    }

    /// Construct a receiver from a contract address.
    pub fn from_contract(address: ContractAddress, function: OwnedReceiveName) -> Self {
        Receiver::Contract {
            address,
            function,
        }
    }

    /// Get the Address of the receiver.
    pub fn address(&self) -> Address {
        match self {
            Receiver::Account {
                address,
                ..
            } => Address::Account(*address),
            Receiver::Contract {
                address,
                ..
            } => Address::Contract(*address),
        }
    }
}

impl From<AccountAddress> for Receiver {
    fn from(address: AccountAddress) -> Self { Self::from_account(address) }
}

/// Additional information to include with a transfer.
#[derive(Debug, Serialize, SchemaType)]
pub struct AdditionalData(#[concordium(size_length = 2)] Vec<u8>);

impl AdditionalData {
    /// Construct an AdditionalData containing no data.
    pub fn empty() -> Self { AdditionalData(Vec::new()) }
}

impl From<Vec<u8>> for AdditionalData {
    fn from(data: Vec<u8>) -> Self { AdditionalData(data) }
}

impl AsRef<[u8]> for AdditionalData {
    fn as_ref(&self) -> &[u8] { &self.0 }
}

/// A single transfer of some amount of a token.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct Transfer<T: IsTokenId> {
    /// The ID of the token being transferred.
    pub token_id: T,
    /// The amount of tokens being transferred.
    pub amount:   TokenAmount,
    /// The address owning the tokens being transferred.
    pub from:     Address,
    /// The address receiving the tokens being transferred.
    pub to:       Receiver,
    /// Additional data to include in the transfer.
    /// Can be used for additional arguments.
    pub data:     AdditionalData,
}

/// The parameter type for the contract function `transfer`.
#[derive(Debug, Serialize, SchemaType)]
pub struct TransferParams<T: IsTokenId>(#[concordium(size_length = 1)] pub Vec<Transfer<T>>);

impl<T: IsTokenId> From<Vec<Transfer<T>>> for TransferParams<T> {
    fn from(transfers: Vec<Transfer<T>>) -> Self { TransferParams(transfers) }
}

impl<T: IsTokenId> AsRef<[Transfer<T>]> for TransferParams<T> {
    fn as_ref(&self) -> &[Transfer<T>] { &self.0 }
}

/// The update to an the operator.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the variants cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub enum OperatorUpdate {
    /// Remove the operator.
    Remove,
    /// Add an address as an operator.
    Add,
}

/// The parameter type for the contract function `updateOperator`.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
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
#[derive(Debug, Serialize, SchemaType)]
pub struct BalanceOfQuery<T: IsTokenId> {
    /// The ID of the token for which to query the balance of.
    pub token_id: T,
    /// The address for which to query the balance of.
    pub address:  Address,
}

/// The parameter type for the contract function `balanceOf`.
/// This is contract function can only be called by another contract instance,
/// and there is no reason to derive a SchemaType for this example.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct BalanceOfQueryParams<T: IsTokenId> {
    /// The contract function to trigger with the results of the queries.
    pub callback: OwnedReceiveName,
    /// List of balance queries.
    #[concordium(size_length = 1)]
    pub queries:  Vec<BalanceOfQuery<T>>,
}

/// BalanceOf query with the result of the query.
pub type BalanceOfQueryResult<T> = (BalanceOfQuery<T>, TokenAmount);

/// The response which is sent back when calling the contract function
/// `balanceOf`.
/// It consists of the list of queries paired with their corresponding result.
#[derive(Debug, Serialize, SchemaType)]
pub struct BalanceOfQueryResponse<T: IsTokenId>(
    #[concordium(size_length = 1)] Vec<BalanceOfQueryResult<T>>,
);

impl<T: IsTokenId> From<Vec<BalanceOfQueryResult<T>>> for BalanceOfQueryResponse<T> {
    fn from(results: Vec<BalanceOfQueryResult<T>>) -> Self { BalanceOfQueryResponse(results) }
}

impl<T: IsTokenId> AsRef<[BalanceOfQueryResult<T>]> for BalanceOfQueryResponse<T> {
    fn as_ref(&self) -> &[BalanceOfQueryResult<T>] { &self.0 }
}

/// The parameter type for a contract function which receives CTS1 tokens.
// Note: For the serialization to be derived according to the CTS1
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct OnReceivingCTS1Params<T: IsTokenId> {
    /// The ID of the token received.
    pub token_id:      T,
    /// The amount of tokens received.
    pub amount:        TokenAmount,
    /// The previous owner of the tokens.
    pub from:          Address,
    /// The name of the token contract which is tracking the token and
    /// implements CTS1.
    pub contract_name: OwnedContractName,
    /// Some extra information which where sent as part of the transfer.
    pub data:          AdditionalData,
}
