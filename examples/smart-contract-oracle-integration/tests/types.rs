use concordium_std::*;

#[derive(Debug, Serial, SchemaType)]
pub struct InitParamsUmbrellaFeeds {
    pub registry:            ContractAddress,
    pub required_signatures: u16,
    pub staking_bank:        ContractAddress,
    pub decimals:            u8,
}

#[derive(Serialize, SchemaType, Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub struct PriceData {
    /// This is a placeholder, that can be used for some additional data.
    pub data:      u8,
    /// The heartbeat specifies the interval in seconds that the price data will
    /// be refreshed in case the price stays flat. ATTENTION: u64 is used
    /// here instead of u24 (different from the original solidity smart
    /// contracts).
    pub heartbeat: u64,
    /// It is the time the validators run consensus to decide on the price data.
    pub timestamp: Timestamp,
    /// The relative price.
    pub price:     u128,
}

/// Part of the parameter type for the contract function `update`.
/// Specifies the message that is signed.
#[derive(SchemaType, Serialize, Clone)]
pub struct Message {
    /// The contract_address that the signature is intended for.
    pub contract_address: ContractAddress,
    /// A timestamp to make signatures expire.
    pub timestamp:        Timestamp,
    /// The price feed.
    pub price_feed:       Vec<(String, PriceData)>,
}

/// The parameter type for the contract function `update` and
/// `view_message_hash`. Takes a vector of signers and signatures, and the
/// message that was signed.
#[derive(Serialize, SchemaType)]
pub struct UpdateParams {
    /// Signers and signatures.
    pub signers_and_signatures: Vec<(PublicKeyEd25519, SignatureEd25519)>,
    /// Message that was signed.
    pub message:                Message,
}

/// The parameter type for the contract function `importContracts`.
#[derive(Serialize, SchemaType)]
#[concordium(transparent)]
pub struct ImportContractsParam {
    /// List of contract addresses.
    #[concordium(size_length = 2)]
    pub entries: Vec<ContractAddress>,
}
