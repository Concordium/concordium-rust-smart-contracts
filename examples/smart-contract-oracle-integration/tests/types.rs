use concordium_std::*;
use smart_contract_oracle_integration::PriceData;

/// Parameter type for the contract function `init` from the `umbrella_feeds`
/// contract (Umbrella oracle protocol).
#[derive(Debug, Serial, SchemaType)]
pub struct InitParamsUmbrellaFeeds {
    /// Registry contract address.
    pub registry:            ContractAddress,
    /// Number of signatures required to update the price data in the oracle.
    pub required_signatures: u16,
    /// Staking bank contract address.
    pub staking_bank:        ContractAddress,
    /// Decimal value for the price data.
    pub decimals:            u8,
}

/// Part of the parameter type for the contract function `update` from the
/// `umbrella_feeds` contract (Umbrella oracle protocol). Specifies the message
/// that is signed.
#[derive(SchemaType, Serialize, Clone)]
pub struct Message {
    /// The contract_address that the signature is intended for.
    pub contract_address: ContractAddress,
    /// A timestamp to make signatures expire.
    pub timestamp:        Timestamp,
    /// The price feed.
    pub price_feed:       Vec<(String, PriceData)>,
}

/// The parameter type for the contract functions `update` and
/// `view_message_hash` from the `umbrella_feeds` contract (Umbrella oracle
/// protocol). Takes a vector of signers and signatures, and the
/// message that was signed.
#[derive(Serialize, SchemaType)]
pub struct UpdateParams {
    /// Signers and signatures.
    pub signers_and_signatures: Vec<(PublicKeyEd25519, SignatureEd25519)>,
    /// Message that was signed.
    pub message:                Message,
}

/// The parameter type for the contract function `importContracts` from the
/// `registry` contract (Umbrella oracle protocol).
#[derive(Serialize, SchemaType)]
#[concordium(transparent)]
pub struct ImportContractsParam {
    /// List of contract addresses.
    #[concordium(size_length = 2)]
    pub entries: Vec<ContractAddress>,
}
