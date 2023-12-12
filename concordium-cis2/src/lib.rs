//! This library provides types and functions for working with the [Concordium
//! Token Standard CIS2](https://proposals.concordium.software/CIS/cis-2.html).
//!
//! It contains types for the parameters for each of the contract functions and
//! types for each event. Each type have implemented serialization according to
//! CIS2.
//! Additionally the crate exports an CIS2Error wrapper type which can be used
//! to wrap and extend a custom error type. This will ensure the CIS2 errors
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
//! ```
//!
//! # Features
//!
//! This crate has features `std` and `u256_amount`. The former one is default.
//! When `u256_amount` feature is enabled the type [`TokenAmountU256`] is
//! defined and implements the [`IsTokenAmount`] interface.
#![cfg_attr(not(feature = "std"), no_std)]

mod cis2_client;
pub use cis2_client::{Cis2Client, Cis2ClientError};

use concordium_std::{collections::BTreeMap, *};
// Re-export for backward compatibility.
pub use concordium_std::MetadataUrl;
#[cfg(not(feature = "std"))]
use core::{fmt, ops};
#[cfg(feature = "std")]
use std::{fmt, ops};

use convert::TryFrom;

/// The standard identifier for the CIS-0: Standard Detection.
pub const CIS0_STANDARD_IDENTIFIER: StandardIdentifier<'static> =
    StandardIdentifier::new_unchecked("CIS-0");

/// The standard identifier for the CIS-1: Concordium Token Standard.
pub const CIS1_STANDARD_IDENTIFIER: StandardIdentifier<'static> =
    StandardIdentifier::new_unchecked("CIS-1");

/// The standard identifier for the CIS-2: Concordium Token Standard 2.
pub const CIS2_STANDARD_IDENTIFIER: StandardIdentifier<'static> =
    StandardIdentifier::new_unchecked("CIS-2");

/// Tag for the CIS2 Transfer event.
pub const TRANSFER_EVENT_TAG: u8 = u8::MAX;
/// Tag for the CIS2 Mint event.
pub const MINT_EVENT_TAG: u8 = u8::MAX - 1;
/// Tag for the CIS2 Burn event.
pub const BURN_EVENT_TAG: u8 = u8::MAX - 2;
/// Tag for the CIS2 UpdateOperator event.
pub const UPDATE_OPERATOR_EVENT_TAG: u8 = u8::MAX - 3;
/// Tag for the CIS2 TokenMetadata event.
pub const TOKEN_METADATA_EVENT_TAG: u8 = u8::MAX - 4;

/// Trait for marking types as CIS2 token IDs.
/// For a type to be a valid CIS2 token ID it must implement
/// `SchemaType` and `Serialize`, such that the first
/// byte indicates how many bytes is used to represent the token ID, followed by
/// this many bytes for the token ID.
///
/// Note: The reason for introducing such a trait instead of representing every
/// token ID using `Vec<u8>` is to allow smart contracts to use specialized
/// token ID implementations avoiding allocations.
pub trait IsTokenId: Serialize + schema::SchemaType {}

/// Trait for marking types as CIS2 token amounts.
/// For a type to be a valid CIS2 token amount it must implement SchemaType and
/// Serialize, using the LEB128 unsigned integer encoding constrained to at most
/// 37 bytes.
///
/// Note: The reason for introducing such a trait instead of representing every
/// token amount using `[u8; 37]` is to allow smart contracts to use specialized
/// token amount implementations avoiding doing arithmetics of large integers.
pub trait IsTokenAmount: Serialize + schema::SchemaType {}

/// Token Identifier, which combined with the address of the contract instance,
/// forms the unique identifier of a token type.
///
/// This token ID type can represent every possible token ID but requires
/// allocating a Vec. Using a fixed size token ID type (such as `TokenIdFixed`)
/// will avoid this.
///
/// The CIS2 specification allows for up to 255 bytes for the token ID, but
/// unless the bytes have some significant meaning, it is most likely better to
/// use a smaller fixed size token ID such as `TokenIdU8`.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Clone, Serialize)]
pub struct TokenIdVec(#[concordium(size_length = 1)] pub Vec<u8>);

impl IsTokenId for TokenIdVec {}

impl schema::SchemaType for TokenIdVec {
    fn get_type() -> schema::Type { schema::Type::ByteList(schema::SizeLength::U8) }
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
/// The CIS2 specification allows for up to 255 bytes for the token ID, but for
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
    fn get_type() -> schema::Type { schema::Type::ByteList(schema::SizeLength::U8) }
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
        out.write_all(&self.0)?;
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
/// The CIS2 specification allows for up to 255 bytes for the token ID, but for
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
    fn get_type() -> schema::Type { schema::Type::ByteList(schema::SizeLength::U8) }
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
/// The CIS2 specification allows for up to 255 bytes for the token ID, but for
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
    fn get_type() -> schema::Type { schema::Type::ByteList(schema::SizeLength::U8) }
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
/// The CIS2 specification allows for up to 255 bytes for the token ID, but for
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
    fn get_type() -> schema::Type { schema::Type::ByteList(schema::SizeLength::U8) }
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
/// The CIS2 specification allows for up to 255 bytes for the token ID, but for
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
    fn get_type() -> schema::Type { schema::Type::ByteList(schema::SizeLength::U8) }
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
/// The CIS2 specification allows for up to 255 bytes for the token ID, but for
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
    fn get_type() -> schema::Type { schema::Type::ByteList(schema::SizeLength::U8) }
}

/// The `TokenIdUnit` is serialized with one byte with the value 0.
impl Serial for TokenIdUnit {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { out.write_u8(0) }
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

macro_rules! token_amount_wrapper {
    ($name:ident, $wrapped:ty) => {
        #[derive(Debug, Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Default)]
        #[repr(transparent)]
        pub struct $name(pub $wrapped);

        impl ops::Add<Self> for $name {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output { $name(self.0 + rhs.0) }
        }

        impl ops::AddAssign for $name {
            fn add_assign(&mut self, other: Self) { *self = *self + other; }
        }

        impl ops::Sub<Self> for $name {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self::Output { $name(self.0 - rhs.0) }
        }

        impl ops::SubAssign for $name {
            fn sub_assign(&mut self, other: Self) { *self = *self - other; }
        }

        impl ops::Mul<$wrapped> for $name {
            type Output = Self;

            fn mul(self, rhs: $wrapped) -> Self::Output { $name(self.0 * rhs) }
        }

        impl ops::Mul<$name> for $wrapped {
            type Output = $name;

            fn mul(self, rhs: $name) -> Self::Output { $name(self * rhs.0) }
        }

        impl ops::MulAssign<$wrapped> for $name {
            fn mul_assign(&mut self, other: $wrapped) { *self = *self * other; }
        }

        impl ops::Rem<$wrapped> for $name {
            type Output = Self;

            fn rem(self, other: $wrapped) -> Self::Output { $name(self.0 % other) }
        }

        impl ops::RemAssign<$wrapped> for $name {
            fn rem_assign(&mut self, other: $wrapped) { *self = *self % other; }
        }

        impl iter::Sum for $name {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.fold($name(0), ops::Add::add) }
        }

        impl IsTokenAmount for $name {}

        /// Uses the ULeb128 encoding with up to 37 bytes for the encoding as
        /// according to CIS-2 specification.
        impl schema::SchemaType for $name {
            fn get_type() -> schema::Type { schema::Type::ULeb128(37) }
        }

        impl Serial for $name {
            fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
                let mut value = self.0;
                loop {
                    let mut byte = (value as u8) & 0b0111_1111;
                    value >>= 7;
                    if value != 0 {
                        byte |= 0b1000_0000;
                    }
                    out.write_u8(byte)?;

                    if value == 0 {
                        return Ok(());
                    }
                }
            }
        }

        impl Deserial for $name {
            fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
                let mut result: $wrapped = 0;
                for i in 0..37 {
                    let byte = source.read_u8()?;
                    let value_byte = (byte & 0b0111_1111) as $wrapped;
                    result = result.checked_add(value_byte << (i * 7)).ok_or(ParseError {})?;

                    if byte & 0b1000_0000 == 0 {
                        return Ok($name(result));
                    }
                }
                Err(ParseError {})
            }
        }

        impl From<$wrapped> for $name {
            fn from(v: $wrapped) -> $name { $name(v) }
        }

        impl From<$name> for $wrapped {
            fn from(v: $name) -> $wrapped { v.0 }
        }
    };
}

token_amount_wrapper!(TokenAmountU128, u128);
token_amount_wrapper!(TokenAmountU64, u64);
token_amount_wrapper!(TokenAmountU32, u32);
token_amount_wrapper!(TokenAmountU16, u16);
token_amount_wrapper!(TokenAmountU8, u8);

#[cfg(feature = "u256_amount")]
mod u256_token {
    use super::*;
    use primitive_types::U256;
    #[derive(Debug, Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Default)]
    #[repr(transparent)]
    #[cfg_attr(docsrs, cfg(feature = "u256_amount"))]
    pub struct TokenAmountU256(pub U256);

    impl ops::Add<Self> for TokenAmountU256 {
        type Output = Self;

        fn add(self, rhs: Self) -> Self::Output { TokenAmountU256(self.0 + rhs.0) }
    }

    impl ops::AddAssign for TokenAmountU256 {
        fn add_assign(&mut self, other: Self) { *self = *self + other; }
    }

    impl ops::Sub<Self> for TokenAmountU256 {
        type Output = Self;

        fn sub(self, rhs: Self) -> Self::Output { TokenAmountU256(self.0 - rhs.0) }
    }

    impl ops::SubAssign for TokenAmountU256 {
        fn sub_assign(&mut self, other: Self) { *self = *self - other; }
    }

    impl ops::Mul<U256> for TokenAmountU256 {
        type Output = Self;

        fn mul(self, rhs: U256) -> Self::Output { TokenAmountU256(self.0 * rhs) }
    }

    impl ops::Mul<TokenAmountU256> for U256 {
        type Output = TokenAmountU256;

        fn mul(self, rhs: TokenAmountU256) -> Self::Output { TokenAmountU256(self * rhs.0) }
    }

    impl ops::MulAssign<U256> for TokenAmountU256 {
        fn mul_assign(&mut self, other: U256) { *self = *self * other; }
    }

    impl ops::Rem<U256> for TokenAmountU256 {
        type Output = Self;

        fn rem(self, other: U256) -> Self::Output { TokenAmountU256(self.0 % other) }
    }

    impl ops::RemAssign<U256> for TokenAmountU256 {
        fn rem_assign(&mut self, other: U256) { *self = *self % other; }
    }

    impl iter::Sum for TokenAmountU256 {
        fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
            iter.fold(TokenAmountU256(U256::zero()), ops::Add::add)
        }
    }

    impl IsTokenAmount for TokenAmountU256 {}

    /// Uses the ULeb128 encoding with up to 37 bytes for the encoding as
    /// according to CIS-2 specification.
    impl schema::SchemaType for TokenAmountU256 {
        fn get_type() -> schema::Type { schema::Type::ULeb128(37) }
    }

    impl Serial for TokenAmountU256 {
        fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
            let mut value = self.0;
            loop {
                let mut byte = (value.low_u32() as u8) & 0b0111_1111;
                value >>= 7;
                if value != U256::zero() {
                    byte |= 0b1000_0000;
                }
                out.write_u8(byte)?;

                if value.is_zero() {
                    return Ok(());
                }
            }
        }
    }

    impl Deserial for TokenAmountU256 {
        fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
            let mut result: U256 = U256::zero();
            for i in 0..36 {
                let byte = source.read_u8()?;
                let value_byte = <U256>::from(byte & 0b0111_1111);
                result = result.checked_add(value_byte << (i * 7)).ok_or(ParseError {})?;
                if byte & 0b1000_0000 == 0 {
                    return Ok(TokenAmountU256(result));
                }
            }
            let byte = source.read_u8()?;
            let value_byte = byte & 0b0111_1111;
            if value_byte & 0b1111_0000 != 0 {
                Err(ParseError {})
            } else {
                let value_byte = <U256>::from(value_byte);
                result = result.checked_add(value_byte << (36 * 7)).ok_or(ParseError {})?;
                if byte & 0b1000_0000 == 0 {
                    Ok(TokenAmountU256(result))
                } else {
                    Err(ParseError {})
                }
            }
        }
    }

    impl From<U256> for TokenAmountU256 {
        fn from(v: U256) -> TokenAmountU256 { TokenAmountU256(v) }
    }

    impl From<TokenAmountU256> for U256 {
        fn from(v: TokenAmountU256) -> U256 { v.0 }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn serial_token_amount256_max_test() {
            let v = TokenAmountU256(U256([u64::MAX; 4]));
            let bytes = to_bytes(&v);
            assert_eq!(Ok(v), from_bytes(&bytes));
        }
        #[test]
        fn serial_token_amount256_0_test() {
            let v = TokenAmountU256(U256([0; 4]));
            let bytes = to_bytes(&v);
            assert_eq!(Ok(v), from_bytes(&bytes));
        }
        #[test]
        fn serial_token_amount_test() {
            let v = TokenAmountU256(U256([u64::MAX, 1, 1, 1]));
            let bytes = to_bytes(&v);
            assert_eq!(Ok(v), from_bytes(&bytes));
        }
        #[test]
        fn serial_token_amount_invalid() {
            // fail if overflowing.
            let mut max = to_bytes(&TokenAmountU256(U256([u64::MAX; 4])));
            max[36] |= 0b1000_0000;
            max.push(0b0000_1111);
            assert_eq!(Err(ParseError {}), from_bytes::<TokenAmountU256>(&max));
        }
    }
}

#[cfg(feature = "u256_amount")]
pub use u256_token::*;

/// An untagged event of a transfer of some amount of tokens from one address to
/// another. For a tagged version, use `Cis2Event`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct TransferEvent<T: IsTokenId, A: IsTokenAmount> {
    /// The ID of the token being transferred.
    pub token_id: T,
    /// The amount of tokens being transferred.
    pub amount:   A,
    /// The address owning these tokens before the transfer.
    pub from:     Address,
    /// The address to receive these tokens after the transfer.
    pub to:       Address,
}

/// An untagged event of tokens being minted, could be a new token type or
/// extending the total supply of existing token.
/// For a tagged version, use `Cis2Event`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct MintEvent<T: IsTokenId, A: IsTokenAmount> {
    /// The ID of the token being minted, (possibly a new token ID).
    pub token_id: T,
    /// The number of tokens being minted, this is allowed to be 0 as well.
    pub amount:   A,
    /// The initial owner of these newly minted amount of tokens.
    pub owner:    Address,
}

/// An untagged event of some amount of a token type being burned.
/// For a tagged version, use `Cis2Event`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct BurnEvent<T: IsTokenId, A: IsTokenAmount> {
    /// The ID of the token where an amount is being burned.
    pub token_id: T,
    /// The amount of tokens being burned.
    pub amount:   A,
    /// The owner of the tokens being burned.
    pub owner:    Address,
}

/// An untagged event of an update to an operator address for an owner address.
/// For a tagged version, use `Cis2Event`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct UpdateOperatorEvent {
    /// The update to the operator.
    pub update:   OperatorUpdate,
    /// The address for whom, the operator is updated.
    pub owner:    Address,
    /// The address who is the operator being updated.
    pub operator: Address,
}

/// An untagged event for setting the metadata for a token.
/// For a tagged version, use `Cis2Event`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct TokenMetadataEvent<T: IsTokenId> {
    /// The ID of the token.
    pub token_id:     T,
    /// The location of the metadata.
    pub metadata_url: MetadataUrl,
}

/// Tagged CIS2 event to be serialized for the event log.
#[derive(Debug, Serialize, PartialEq, Eq)]
#[concordium(repr(u8))]
pub enum Cis2Event<T: IsTokenId, A: IsTokenAmount> {
    /// A transfer between two addresses of some amount of tokens.
    #[concordium(tag = 255)]
    Transfer(TransferEvent<T, A>),
    /// Creation of new tokens, could be both adding some amounts to an existing
    /// token or introduce an entirely new token ID.
    #[concordium(tag = 254)]
    Mint(MintEvent<T, A>),
    /// Destruction of tokens removing some amounts of a token.
    #[concordium(tag = 253)]
    Burn(BurnEvent<T, A>),
    /// Updates to an operator for a specific address and token id.
    #[concordium(tag = 252)]
    UpdateOperator(UpdateOperatorEvent),
    /// Setting the metadata for a token.
    #[concordium(tag = 251)]
    TokenMetadata(TokenMetadataEvent<T>),
}

// Implemented manually to use named fields in the schema thereby simplifying
// it.
impl<T: IsTokenId, A: IsTokenAmount> schema::SchemaType for Cis2Event<T, A> {
    fn get_type() -> schema::Type {
        let mut event_map = BTreeMap::new();
        event_map.insert(
            TRANSFER_EVENT_TAG,
            (
                "Transfer".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), T::get_type()),
                    (String::from("amount"), A::get_type()),
                    (String::from("from"), Address::get_type()),
                    (String::from("to"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            MINT_EVENT_TAG,
            (
                "Mint".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), T::get_type()),
                    (String::from("amount"), A::get_type()),
                    (String::from("owner"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            BURN_EVENT_TAG,
            (
                "Burn".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), T::get_type()),
                    (String::from("amount"), A::get_type()),
                    (String::from("owner"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            UPDATE_OPERATOR_EVENT_TAG,
            (
                "UpdateOperator".to_string(),
                schema::Fields::Named(vec![
                    (String::from("update"), OperatorUpdate::get_type()),
                    (String::from("owner"), Address::get_type()),
                    (String::from("operator"), Address::get_type()),
                ]),
            ),
        );
        event_map.insert(
            TOKEN_METADATA_EVENT_TAG,
            (
                "TokenMetadata".to_string(),
                schema::Fields::Named(vec![
                    (String::from("token_id"), T::get_type()),
                    (String::from("metadata_url"), MetadataUrl::get_type()),
                ]),
            ),
        );
        schema::Type::TaggedEnum(event_map)
    }
}

/// The different errors the contract can produce.
#[derive(Debug, PartialEq, Eq, SchemaType, Serial, Deserial)]
pub enum Cis2Error<R> {
    /// Invalid token id (Error code: -42000001).
    InvalidTokenId,
    /// The balance of the token owner is insufficient for the transfer (Error
    /// code: -42000002).
    InsufficientFunds,
    /// Sender is unauthorized to call this function (Error code: -42000003).
    Unauthorized,
    /// Custom error
    Custom(R),
}

/// Convert `Cis2Error` into a reject with error code:
/// - InvalidTokenId: -42000001
/// - InsufficientFunds: -42000002
/// - Unauthorized: -42000003
/// - Custom: The error code of `R`.
///
/// Also serializes the `Cis2Error` and adds it as the return value.
impl<R: Into<Reject> + Serial> From<Cis2Error<R>> for Reject {
    fn from(err: Cis2Error<R>) -> Self {
        let return_value = Some(to_bytes(&err));
        let error_code = match err {
            Cis2Error::InvalidTokenId => unsafe {
                crate::num::NonZeroI32::new_unchecked(-42000001)
            },
            Cis2Error::InsufficientFunds => unsafe {
                crate::num::NonZeroI32::new_unchecked(-42000002)
            },
            Cis2Error::Unauthorized => unsafe { crate::num::NonZeroI32::new_unchecked(-42000003) },
            Cis2Error::Custom(reject) => reject.into().error_code,
        };
        Self {
            error_code,
            return_value,
        }
    }
}

impl<X> From<LogError> for Cis2Error<X>
where
    X: From<LogError>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: LogError) -> Self { Cis2Error::Custom(X::from(err)) }
}

impl<X> From<ParseError> for Cis2Error<X>
where
    X: From<ParseError>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: ParseError) -> Self { Cis2Error::Custom(X::from(err)) }
}

impl<T, X> From<CallContractError<T>> for Cis2Error<X>
where
    X: From<CallContractError<T>>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: CallContractError<T>) -> Self { Cis2Error::Custom(X::from(err)) }
}

impl<X> From<TransferError> for Cis2Error<X>
where
    X: From<TransferError>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: TransferError) -> Self { Cis2Error::Custom(X::from(err)) }
}

impl<X> From<UpgradeError> for Cis2Error<X>
where
    X: From<UpgradeError>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: UpgradeError) -> Self { Cis2Error::Custom(X::from(err)) }
}

impl<X> From<QueryAccountBalanceError> for Cis2Error<X>
where
    X: From<QueryAccountBalanceError>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: QueryAccountBalanceError) -> Self { Cis2Error::Custom(X::from(err)) }
}

impl<X> From<QueryContractBalanceError> for Cis2Error<X>
where
    X: From<QueryContractBalanceError>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: QueryContractBalanceError) -> Self { Cis2Error::Custom(X::from(err)) }
}

impl<X> From<NewReceiveNameError> for Cis2Error<X>
where
    X: From<NewReceiveNameError>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: NewReceiveNameError) -> Self { Cis2Error::Custom(X::from(err)) }
}

impl<X> From<CheckAccountSignatureError> for Cis2Error<X>
where
    X: From<CheckAccountSignatureError>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: CheckAccountSignatureError) -> Self { Cis2Error::Custom(X::from(err)) }
}

impl<X> From<QueryAccountPublicKeysError> for Cis2Error<X>
where
    X: From<QueryAccountPublicKeysError>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: QueryAccountPublicKeysError) -> Self { Cis2Error::Custom(X::from(err)) }
}

impl<X> From<NewContractNameError> for Cis2Error<X>
where
    X: From<NewContractNameError>,
{
    #[inline]
    /// Converts the error by wrapping it in [Self::Custom].
    fn from(err: NewContractNameError) -> Self { Cis2Error::Custom(X::from(err)) }
}

/// The receiving address for a transfer, similar to the Address type, but
/// contains extra information when the receiver address is a contract.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the variants and the order of their fields
// cannot be changed.
#[derive(Debug, Serialize, Clone, SchemaType)]
pub enum Receiver {
    /// The receiver is an account address.
    Account(
        /// The receiving address.
        AccountAddress,
    ),
    /// The receiver is a contract address.
    Contract(
        /// The receiving address.
        ContractAddress,
        /// The function to call on the receiving contract.
        OwnedEntrypointName,
    ),
}

impl Receiver {
    /// Construct a receiver from an account address.
    pub fn from_account(address: AccountAddress) -> Self { Receiver::Account(address) }

    /// Construct a receiver from a contract address.
    pub fn from_contract(address: ContractAddress, function: OwnedEntrypointName) -> Self {
        Receiver::Contract(address, function)
    }

    /// Get the Address of the receiver.
    pub fn address(&self) -> Address {
        match self {
            Receiver::Account(address) => Address::Account(*address),
            Receiver::Contract(address, ..) => Address::Contract(*address),
        }
    }
}

impl From<AccountAddress> for Receiver {
    fn from(address: AccountAddress) -> Self { Self::from_account(address) }
}

/// Additional information to include with a transfer.
#[derive(Debug, Serialize, Clone)]
#[concordium(transparent)]
pub struct AdditionalData(#[concordium(size_length = 2)] Vec<u8>);

// Implemented manually to display the AdditionalData as a hex string.
impl schema::SchemaType for AdditionalData {
    fn get_type() -> schema::Type { schema::Type::ByteList(schema::SizeLength::U16) }
}

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
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, Clone, SchemaType)]
pub struct Transfer<T: IsTokenId, A: IsTokenAmount> {
    /// The ID of the token being transferred.
    pub token_id: T,
    /// The amount of tokens being transferred.
    pub amount:   A,
    /// The address owning the tokens being transferred.
    pub from:     Address,
    /// The address receiving the tokens being transferred.
    pub to:       Receiver,
    /// Additional data to include in the transfer.
    /// Can be used for additional arguments.
    pub data:     AdditionalData,
}

/// The parameter type for the contract function `transfer`.
#[derive(Debug, Serialize, Clone, SchemaType)]
#[concordium(transparent)]
pub struct TransferParams<T: IsTokenId, A: IsTokenAmount>(
    #[concordium(size_length = 2)] pub Vec<Transfer<T, A>>,
);

impl<T: IsTokenId, A: IsTokenAmount> From<Vec<Transfer<T, A>>> for TransferParams<T, A> {
    fn from(transfers: Vec<Transfer<T, A>>) -> Self { TransferParams(transfers) }
}

impl<T: IsTokenId, A: IsTokenAmount> AsRef<[Transfer<T, A>]> for TransferParams<T, A> {
    fn as_ref(&self) -> &[Transfer<T, A>] { &self.0 }
}

/// The update to an the operator.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the variants cannot be changed.
#[derive(Debug, Serialize, Clone, Copy, SchemaType, PartialEq, Eq)]
pub enum OperatorUpdate {
    /// Remove the operator.
    Remove,
    /// Add an address as an operator.
    Add,
}

/// A single update of an operator.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, Clone, SchemaType, PartialEq, Eq)]
pub struct UpdateOperator {
    /// The update for this operator.
    pub update:   OperatorUpdate,
    /// The address which is either added or removed as an operator.
    /// Note: The address for whom this will become an operator is the sender of
    /// the contract transaction.
    pub operator: Address,
}

/// The parameter type for the contract function `updateOperator`.
#[derive(Debug, Serialize, Clone, SchemaType)]
#[concordium(transparent)]
pub struct UpdateOperatorParams(#[concordium(size_length = 2)] pub Vec<UpdateOperator>);

/// A query for the balance of a given address for a given token.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct BalanceOfQuery<T: IsTokenId> {
    /// The ID of the token for which to query the balance of.
    pub token_id: T,
    /// The address for which to query the balance of.
    pub address:  Address,
}

/// The parameter type for the contract function `balanceOf`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct BalanceOfQueryParams<T: IsTokenId> {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<BalanceOfQuery<T>>,
}

/// The response which is sent back when calling the contract function
/// `balanceOf`.
/// It consists of the list of results corresponding to the list of queries.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
#[concordium(transparent)]
pub struct BalanceOfQueryResponse<A: IsTokenAmount>(#[concordium(size_length = 2)] pub Vec<A>);

impl<A: IsTokenAmount> From<Vec<A>> for BalanceOfQueryResponse<A> {
    fn from(results: Vec<A>) -> Self { BalanceOfQueryResponse(results) }
}

impl<A: IsTokenAmount> AsRef<[A]> for BalanceOfQueryResponse<A> {
    fn as_ref(&self) -> &[A] { &self.0 }
}

/// A query for the operator of a given address for a given token.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct OperatorOfQuery {
    /// The owner address to inspect.
    pub owner:   Address,
    /// The address for which to check for being an operator of the owner.
    pub address: Address,
}

/// The parameter type for the contract function `operatorOf`.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct OperatorOfQueryParams {
    /// List of operatorOf queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<OperatorOfQuery>,
}

/// The response which is sent back when calling the contract function
/// `operatorOf`.
/// It consists of the list of result in the same order and length as the
/// queries in the parameter.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
#[concordium(transparent)]
pub struct OperatorOfQueryResponse(#[concordium(size_length = 2)] pub Vec<bool>);

impl From<Vec<bool>> for OperatorOfQueryResponse {
    fn from(results: Vec<bool>) -> Self { OperatorOfQueryResponse(results) }
}

impl AsRef<[bool]> for OperatorOfQueryResponse {
    fn as_ref(&self) -> &[bool] { &self.0 }
}

/// The parameter type for the contract function `tokenMetadata`.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct TokenMetadataQueryParams<T: IsTokenId> {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<T>,
}

/// The response which is sent back when calling the contract function
/// `tokenMetadata`.
/// It consists of the list of results corresponding to the list of queries.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct TokenMetadataQueryResponse(#[concordium(size_length = 2)] pub Vec<MetadataUrl>);

impl From<Vec<MetadataUrl>> for TokenMetadataQueryResponse {
    fn from(results: Vec<MetadataUrl>) -> Self { TokenMetadataQueryResponse(results) }
}

impl AsRef<[MetadataUrl]> for TokenMetadataQueryResponse {
    fn as_ref(&self) -> &[MetadataUrl] { &self.0 }
}

/// Generic parameter type for a contract function which receives CIS2 tokens.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub struct OnReceivingCis2Params<T, A> {
    /// The ID of the token received.
    pub token_id: T,
    /// The amount of tokens received.
    pub amount:   A,
    /// The previous owner of the tokens.
    pub from:     Address,
    /// Some extra information which was sent as part of the transfer.
    pub data:     AdditionalData,
}

/// Specific parameter type for a contract function which receives CIS2 tokens
/// with a specific type D for the AdditionalData.
// Note: For the serialization to be derived according to the CIS2
// specification, the order of the fields cannot be changed.
#[derive(Debug, SchemaType)]
pub struct OnReceivingCis2DataParams<T, A, D> {
    /// The ID of the token received.
    pub token_id: T,
    /// The amount of tokens received.
    pub amount:   A,
    /// The previous owner of the tokens.
    pub from:     Address,
    /// Some extra information which was sent as part of the transfer.
    pub data:     D,
}

/// Deserial trait for OnReceivingCis2DataParams<T, A, D>.
impl<T: Deserial, A: Deserial, D: Deserial> Deserial for OnReceivingCis2DataParams<T, A, D> {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let params: OnReceivingCis2Params<T, A> = source.get()?;
        let additional_data_type: D = from_bytes(params.data.as_ref())?;
        Ok(OnReceivingCis2DataParams {
            token_id: params.token_id,
            amount:   params.amount,
            from:     params.from,
            data:     additional_data_type,
        })
    }
}

/// Serial trait for OnReceivingCis2DataParams<T, A, D>.
impl<T: Serial, A: Serial, D: Serial> Serial for OnReceivingCis2DataParams<T, A, D> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.token_id.serial(out)?;
        self.amount.serial(out)?;
        self.from.serial(out)?;
        let add = AdditionalData(to_bytes(&self.data));
        add.serial(out)?;
        Ok(())
    }
}

/// Identifier for a smart contract standard.
/// Consists of a string of ASCII characters up to a length of 255.
///
/// See [StandardIdentifierOwned] for the owned version.
#[derive(Debug, Serial, PartialEq, Eq)]
pub struct StandardIdentifier<'a> {
    #[concordium(size_length = 1)]
    id: &'a str,
}

/// String is not a valid standard identifier. Ensure the length is less than
/// 256 and it only contains ASCII characters.
#[derive(Default)]
pub struct InvalidStandardIdentifierError;

impl<'a> StandardIdentifier<'a> {
    /// Validate and construct a standard identifier.
    pub fn new(id: &'a str) -> Result<Self, InvalidStandardIdentifierError> {
        if id.len() > 255 || !id.is_ascii() {
            Err(InvalidStandardIdentifierError)
        } else {
            Ok(Self {
                id,
            })
        }
    }

    /// Construct a standard identifier without validation.
    pub const fn new_unchecked(id: &'a str) -> Self {
        Self {
            id,
        }
    }

    /// Convert to owned standard identifier.
    pub fn to_owned(&self) -> StandardIdentifierOwned {
        StandardIdentifierOwned::new_unchecked(self.id.to_string())
    }
}

/// Owned identifier for a smart contract standard.
/// Consists of a string of ASCII characters up to a length of 255.
///
/// See [StandardIdentifier] for the borrowed version.
#[derive(Debug, Serialize, PartialEq, Eq, SchemaType)]
#[concordium(transparent)]
pub struct StandardIdentifierOwned {
    #[concordium(size_length = 1)]
    id: String,
}

impl StandardIdentifierOwned {
    /// Validate and construct a standard identifier.
    pub fn new(id: String) -> Result<Self, InvalidStandardIdentifierError> {
        if id.len() > 255 || !id.is_ascii() {
            Err(InvalidStandardIdentifierError)
        } else {
            Ok(Self {
                id,
            })
        }
    }

    /// Construct a standard identifier without validation.
    pub fn new_unchecked(id: String) -> Self {
        Self {
            id,
        }
    }

    /// Convert to standard identifier.
    pub fn as_standard_identifier(&self) -> StandardIdentifier {
        StandardIdentifier::new_unchecked(&self.id)
    }
}

/// The parameter type for the contract function `supports`.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct SupportsQueryParams {
    /// The list of support queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<StandardIdentifierOwned>,
}

/// The query result type for whether a smart contract supports a standard.
// Note: For the serialization to be derived according to the CIS0
// specification, the order of the variants and their fields cannot be changed.
#[derive(Debug, Serialize, SchemaType)]
pub enum SupportResult {
    /// The standard is not supported.
    NoSupport,
    /// The standard is supported by the current contract address.
    Support,
    /// The standard is supported by using another contract address.
    SupportBy(#[concordium(size_length = 1)] Vec<ContractAddress>),
}

/// The response which is sent back when calling the contract function
/// `supports`. It consists of a list of results corresponding to the list of
/// queries.
#[derive(Debug, Serialize, SchemaType)]
#[concordium(transparent)]
pub struct SupportsQueryResponse {
    /// List of support results corresponding to the list of queries.
    #[concordium(size_length = 2)]
    pub results: Vec<SupportResult>,
}

impl From<Vec<SupportResult>> for SupportsQueryResponse {
    fn from(results: Vec<SupportResult>) -> Self {
        SupportsQueryResponse {
            results,
        }
    }
}

impl AsRef<[SupportResult]> for SupportsQueryResponse {
    fn as_ref(&self) -> &[SupportResult] { &self.results }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn serial_token_amount128_127_test() {
        let amount = TokenAmountU128::from(127);
        let bytes = to_bytes(&amount);
        assert_eq!(bytes, vec![127])
    }

    #[test]
    fn serial_token_amount128_max_test() {
        let amount = TokenAmountU128::from(u128::MAX);
        let bytes = to_bytes(&amount);
        assert_eq!(bytes, vec![
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 0b00000011
        ])
    }

    #[test]
    fn deserial_token_amount128_127_test() {
        let amount: TokenAmountU128 = from_bytes(&[127]).expect("Failed to parse bytes");
        assert_eq!(amount, TokenAmountU128::from(127))
    }

    #[test]
    fn deserial_token_amount128_max_test() {
        let amount: TokenAmountU128 = from_bytes(&[
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 0b00000011,
        ])
        .expect("Failed to parse bytes");
        assert_eq!(amount, TokenAmountU128::from(u128::MAX))
    }

    #[test]
    fn serial_token_amount64_127_test() {
        let amount = TokenAmountU64::from(127);
        let bytes = to_bytes(&amount);
        assert_eq!(bytes, vec![127])
    }

    #[test]
    fn serial_token_amount64_max_test() {
        let amount = TokenAmountU64::from(u64::MAX);
        let bytes = to_bytes(&amount);
        assert_eq!(bytes, vec![255, 255, 255, 255, 255, 255, 255, 255, 255, 0b00000001])
    }

    #[test]
    fn deserial_token_amount64_127_test() {
        let amount: TokenAmountU64 = from_bytes(&[127]).expect("Failed to parse bytes");
        assert_eq!(amount, TokenAmountU64::from(127))
    }

    #[test]
    fn deserial_token_amount64_max_test() {
        let amount: TokenAmountU64 =
            from_bytes(&[255, 255, 255, 255, 255, 255, 255, 255, 255, 0b00000001])
                .expect("Failed to parse bytes");
        assert_eq!(amount, TokenAmountU64::from(u64::MAX))
    }

    #[test]
    fn serial_token_amount32_127_test() {
        let amount = TokenAmountU32::from(127);
        let bytes = to_bytes(&amount);
        assert_eq!(bytes, vec![127])
    }

    #[test]
    fn serial_token_amount32_max_test() {
        let amount = TokenAmountU32::from(u32::MAX);
        let bytes = to_bytes(&amount);
        assert_eq!(bytes, vec![255, 255, 255, 255, 0b00001111])
    }

    #[test]
    fn deserial_token_amount32_127_test() {
        let amount: TokenAmountU32 = from_bytes(&[127]).expect("Failed to parse bytes");
        assert_eq!(amount, TokenAmountU32::from(127))
    }

    #[test]
    fn deserial_token_amount32_max_test() {
        let amount: TokenAmountU32 =
            from_bytes(&[255, 255, 255, 255, 0b00001111]).expect("Failed to parse bytes");
        assert_eq!(amount, TokenAmountU32::from(u32::MAX))
    }

    #[test]
    fn serial_token_amount16_127_test() {
        let amount = TokenAmountU16::from(127);
        let bytes = to_bytes(&amount);
        assert_eq!(bytes, vec![127])
    }

    #[test]
    fn serial_token_amount16_max_test() {
        let amount = TokenAmountU16::from(u16::MAX);
        let bytes = to_bytes(&amount);
        assert_eq!(bytes, vec![255, 255, 0b00000011])
    }

    #[test]
    fn deserial_token_amount16_127_test() {
        let amount: TokenAmountU16 = from_bytes(&[127]).expect("Failed to parse bytes");
        assert_eq!(amount, TokenAmountU16::from(127))
    }

    #[test]
    fn deserial_token_amount16_max_test() {
        let amount: TokenAmountU16 =
            from_bytes(&[255, 255, 0b00000011]).expect("Failed to parse bytes");
        assert_eq!(amount, TokenAmountU16::from(u16::MAX))
    }

    #[test]
    fn serial_token_amount8_127_test() {
        let amount = TokenAmountU8::from(127);
        let bytes = to_bytes(&amount);
        assert_eq!(bytes, vec![127])
    }

    #[test]
    fn serial_token_amount8_max_test() {
        let amount = TokenAmountU8::from(u8::MAX);
        let bytes = to_bytes(&amount);
        assert_eq!(bytes, vec![255, 0b00000001])
    }

    #[test]
    fn deserial_token_amount8_127_test() {
        let amount: TokenAmountU8 = from_bytes(&[127]).expect("Failed to parse bytes");
        assert_eq!(amount, TokenAmountU8::from(127))
    }

    #[test]
    fn deserial_token_amount8_max_test() {
        let amount: TokenAmountU8 = from_bytes(&[255, 0b00000001]).expect("Failed to parse bytes");
        assert_eq!(amount, TokenAmountU8::from(u8::MAX))
    }
}
