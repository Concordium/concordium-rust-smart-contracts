//! Defines parameters for Marketplace contract. 
//! [Read more](https://developer.concordium.software/en/mainnet/smart-contracts/general/develop-contracts.html#working-with-parameters) about working with parameters

use concordium_std::{
    AccountAddress, Amount, ContractAddress, Deserial, SchemaType, Serial, Serialize,
};

use crate::{state::TokenListItem, ContractTokenAmount, ContractTokenId};

#[derive(Serial, Deserial, SchemaType)]
pub(crate) struct AddParams {
    pub nft_contract_address: ContractAddress,
    pub token_id: ContractTokenId,

    /// Price per Unit of Token at this the Token is to be sold.
    /// This includes Selling Price + Marketplace Commission
    pub price: Amount,
    pub royalty: u16,

    /// Quantity of the token which can be listed on the marketplace
    /// In case of an NFT this will always be one
    pub quantity: ContractTokenAmount,
}

#[derive(Serial, Deserial, SchemaType)]
pub(crate) struct TransferParams {
    pub nft_contract_address: ContractAddress,
    pub token_id: ContractTokenId,
    pub to: AccountAddress,
    pub owner: AccountAddress,
    pub quantity: ContractTokenAmount,
}

#[derive(Debug, Serialize, SchemaType)]
pub struct TokenList(
    #[concordium(size_length = 2)] pub Vec<TokenListItem<ContractTokenId, ContractTokenAmount>>,
);

#[derive(Serial, Deserial, SchemaType)]
pub struct InitParams {
    pub commission: u16,
}
