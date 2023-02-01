//! Defines the State (persisted data) for the contract.

#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::{IsTokenAmount, IsTokenId};
use concordium_std::*;

#[derive(Clone, Serialize, PartialEq, Eq, Debug)]
pub struct TokenInfo<T: Serial + Deserial> {
    pub id:      T,
    pub address: ContractAddress,
}

#[derive(Clone, Serialize, PartialEq, Eq, Debug)]
pub struct TokenOwnerInfo<T: Serial + Deserial> {
    pub id:      T,
    pub address: ContractAddress,
    pub owner:   AccountAddress,
}

impl<T: Serial + Deserial + Copy> TokenOwnerInfo<T> {
    pub fn from(token_info: &TokenInfo<T>, owner: &AccountAddress) -> Self {
        TokenOwnerInfo {
            owner:   *owner,
            id:      token_info.id,
            address: token_info.address,
        }
    }
}

#[derive(Clone, Serialize, Copy, PartialEq, Eq, Debug)]
pub struct TokenPriceState<A: IsTokenAmount> {
    pub quantity: A,
    pub price:    Amount,
}

#[derive(Clone, Serialize, Copy, PartialEq, Eq, Debug)]
pub struct TokenRoyaltyState {
    /// Primary Owner (Account Address which added the token first time on a
    /// Marketplace Instance)
    pub primary_owner: AccountAddress,

    /// Royalty basis points. Royalty percentage * 100.
    /// This can me atmost equal to 100*100 = 10000(MAX_BASIS_POINTS)
    pub royalty: u16,
}

/// Marketplace Commission
#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
pub(crate) struct Commission {
    /// Commission basis points. equals to percent * 100
    pub(crate) percentage_basis: u16,
}

#[derive(Debug, Serialize, SchemaType, PartialEq, Eq, Clone)]
pub struct TokenListItem<T: IsTokenId, A: IsTokenAmount> {
    pub token_id:      T,
    pub contract:      ContractAddress,
    pub price:         Amount,
    pub owner:         AccountAddress,
    pub royalty:       u16,
    pub primary_owner: AccountAddress,
    pub quantity:      A,
}

#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
pub(crate) struct State<S, T, A>
where
    S: HasStateApi,
    T: IsTokenId,
    A: IsTokenAmount + Copy, {
    pub(crate) commission:      Commission,
    pub(crate) token_royalties: StateMap<TokenInfo<T>, TokenRoyaltyState, S>,
    pub(crate) token_prices:    StateMap<TokenOwnerInfo<T>, TokenPriceState<A>, S>,
}

impl<S: HasStateApi, T: IsTokenId + Copy, A: IsTokenAmount + Copy + ops::Sub<Output = A>>
    State<S, T, A>
{
    pub(crate) fn new(state_builder: &mut StateBuilder<S>, commission: u16) -> Self {
        State {
            commission:      Commission {
                percentage_basis: commission,
            },
            token_royalties: state_builder.new_map(),
            token_prices:    state_builder.new_map(),
        }
    }

    pub(crate) fn list_token(
        &mut self,
        token_info: &TokenInfo<T>,
        owner: &AccountAddress,
        price: Amount,
        royalty: u16,
        quantity: A,
    ) {
        match self.token_royalties.get(token_info) {
            Some(_) => None,
            None => self.token_royalties.insert(token_info.clone(), TokenRoyaltyState {
                primary_owner: *owner,
                royalty,
            }),
        };

        self.token_prices.insert(TokenOwnerInfo::from(token_info, owner), TokenPriceState {
            price,
            quantity,
        });
    }

    pub(crate) fn decrease_listed_quantity(&mut self, token_info: &TokenOwnerInfo<T>, delta: A) {
        let price = match self.token_prices.get(token_info) {
            Option::None => return,
            Option::Some(price) => price,
        };

        self.token_prices.insert(token_info.clone(), TokenPriceState {
            quantity: price.quantity - delta,
            price:    price.price,
        });
    }

    pub(crate) fn get_listed(
        &self,
        token_info: &TokenInfo<T>,
        owner: &AccountAddress,
    ) -> Option<(TokenRoyaltyState, TokenPriceState<A>)> {
        match self.token_royalties.get(token_info) {
            Some(r) => {
                self.token_prices.get(&TokenOwnerInfo::from(token_info, owner)).map(|p| (*r, *p))
            }
            None => Option::None,
        }
    }

    pub(crate) fn list(&self) -> Vec<TokenListItem<T, A>> {
        self.token_prices
            .iter()
            .filter_map(|p| -> Option<TokenListItem<T, A>> {
                let token_info = TokenInfo {
                    id:      p.0.id,
                    address: p.0.address,
                };

                match self.token_royalties.get(&token_info) {
                    Option::None => Option::None,
                    Option::Some(r) => Option::Some(TokenListItem {
                        token_id:      token_info.id,
                        contract:      token_info.address,
                        price:         p.1.price,
                        owner:         p.0.owner,
                        royalty:       r.royalty,
                        primary_owner: r.primary_owner,
                        quantity:      p.1.quantity,
                    }),
                }
            })
            .collect()
    }
}
