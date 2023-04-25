//! Marketplace Contract
//! This module provides implementation of the marketplace contract.
//! Marketplace Contract provides following functions
//! - `list` : returns a list of buyable tokens added to the contract instance.
//! - `add` : adds the token to the list of buyable tokens taking the price of
//!   the token as input.
//! - `transfer` : transfer the authority of the input listed token from one
//!   address to another.
//!
//! This code has not been checked for production readiness. Please use for
//! reference purposes
mod cis2_client;
mod errors;
mod params;
mod state;

use cis2_client::Cis2Client;
use concordium_cis2::{IsTokenAmount, IsTokenId, TokenAmountU64, TokenIdU8};
use concordium_std::*;
use errors::MarketplaceError;
use params::{AddParams, InitParams, TokenList};
use state::{Commission, State, TokenInfo, TokenListItem, TokenRoyaltyState};

use crate::{params::TransferParams, state::TokenOwnerInfo};

type ContractResult<A> = Result<A, MarketplaceError>;

const MAX_BASIS_POINTS: u16 = 10000;

/// Type of token Id used by the CIS2 contract.
type ContractTokenId = TokenIdU8;

/// Type of Token Amount used by the CIS2 contract.
type ContractTokenAmount = TokenAmountU64;

/// Type of state.
type ContractState<S> = State<S, ContractTokenId, ContractTokenAmount>;

/// Initializes a new Marketplace Contract
///
/// This function can be called by using InitParams.
/// The commission should be less than the maximum allowed value of 10000 basis
/// points
#[init(contract = "Market-NFT", parameter = "InitParams")]
fn init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
) -> InitResult<State<S, ContractTokenId, ContractTokenAmount>> {
    let params: InitParams =
        ctx.parameter_cursor().get().map_err(|_e| MarketplaceError::ParseParams)?;

    ensure!(params.commission <= MAX_BASIS_POINTS, MarketplaceError::InvalidCommission.into());

    Ok(State::new(state_builder, params.commission))
}

#[receive(contract = "Market-NFT", name = "add", parameter = "AddParams", mutable)]
fn add<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<ContractState<S>, StateApiType = S>,
) -> ContractResult<()> {
    let params: AddParams =
        ctx.parameter_cursor().get().map_err(|_e| MarketplaceError::ParseParams)?;

    let sender_account_address: AccountAddress = match ctx.sender() {
        Address::Account(account_address) => account_address,
        Address::Contract(_) => bail!(MarketplaceError::CalledByAContract),
    };

    let token_info = TokenInfo {
        address: params.cis_contract_address,
        id:      params.token_id,
    };

    ensure_supports_cis2(host, &params.cis_contract_address)?;
    ensure_is_operator(host, ctx, &params.cis_contract_address)?;
    ensure_balance(
        host,
        params.token_id,
        &params.cis_contract_address,
        sender_account_address,
        params.quantity,
    )?;

    ensure!(
        host.state().commission.percentage_basis + params.royalty <= MAX_BASIS_POINTS,
        MarketplaceError::InvalidRoyalty
    );
    host.state_mut().list_token(
        &token_info,
        &sender_account_address,
        params.price,
        params.royalty,
        params.quantity,
    );

    Ok(())
}

/// Allows for transferring the token specified by TransferParams.
///
/// This function is the typical buuy function of a Marketplace where one
/// account can transfer an Asset by paying a price. The transfer will fail of
/// the Amount paid is < token_quantity * token_price
#[receive(
    contract = "Market-NFT",
    name = "transfer",
    parameter = "TransferParams",
    mutable,
    payable
)]
fn transfer<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<ContractState<S>, StateApiType = S>,
    amount: Amount,
) -> ContractResult<()> {
    let params: TransferParams =
        ctx.parameter_cursor().get().map_err(|_e| MarketplaceError::ParseParams)?;

    let token_info = &TokenInfo {
        id:      params.token_id,
        address: params.cis_contract_address,
    };

    let listed_token = host
        .state()
        .get_listed(token_info, &params.owner)
        .ok_or(MarketplaceError::TokenNotListed)?;

    let listed_quantity = listed_token.1.quantity;
    let price_per_unit = listed_token.1.price;
    let token_royalty_state = listed_token.0;

    ensure!(listed_quantity.cmp(&params.quantity).is_ge(), MarketplaceError::InvalidTokenQuantity);

    let price = price_per_unit * params.quantity.0;
    ensure!(amount.cmp(&price).is_ge(), MarketplaceError::InvalidAmountPaid);

    Cis2Client::transfer(
        host,
        params.token_id,
        params.cis_contract_address,
        params.quantity,
        params.owner,
        concordium_cis2::Receiver::Account(params.to),
    )
    .map_err(MarketplaceError::Cis2ClientError)?;

    distribute_amounts(host, amount, &params.owner, &token_royalty_state, &ctx.owner())?;

    host.state_mut().decrease_listed_quantity(
        &TokenOwnerInfo::from(token_info, &params.owner),
        params.quantity,
    );
    Ok(())
}

/// Returns a list of Added Tokens with Metadata which contains the token price
#[receive(contract = "Market-NFT", name = "list", return_value = "TokenList")]
fn list<S: HasStateApi>(
    _ctx: &impl HasReceiveContext,
    host: &impl HasHost<ContractState<S>, StateApiType = S>,
) -> ContractResult<TokenList> {
    let tokens: Vec<TokenListItem<ContractTokenId, ContractTokenAmount>> = host
        .state()
        .list()
        .iter()
        .filter(|t| t.quantity.cmp(&ContractTokenAmount::from(0)).is_gt())
        .cloned()
        .collect::<Vec<TokenListItem<ContractTokenId, ContractTokenAmount>>>();

    Ok(TokenList(tokens))
}

struct DistributableAmounts {
    to_primary_owner: Amount,
    to_seller:        Amount,
    to_marketplace:   Amount,
}

/// Calls the [supports](https://proposals.concordium.software/CIS/cis-0.html#supports) function of CIS2 contract.
/// Returns error If the contract does not support the standard.
fn ensure_supports_cis2<S: HasStateApi, T: IsTokenId + Copy, A: IsTokenAmount + Copy>(
    host: &mut impl HasHost<State<S, T, A>, StateApiType = S>,
    cis_contract_address: &ContractAddress,
) -> ContractResult<()> {
    let supports_cis2 = Cis2Client::supports_cis2(host, cis_contract_address)
        .map_err(MarketplaceError::Cis2ClientError)?;
    ensure!(supports_cis2, MarketplaceError::CollectionNotCis2);
    Ok(())
}

/// Calls the [operatorOf](https://proposals.concordium.software/CIS/cis-2.html#operatorof) function of CIS contract.
/// Returns error if Current Contract Address is not an Operator of Transaction
/// Sender.
fn ensure_is_operator<S: HasStateApi, T: IsTokenId + Copy, A: IsTokenAmount + Copy>(
    host: &mut impl HasHost<State<S, T, A>, StateApiType = S>,
    ctx: &impl HasReceiveContext<()>,
    cis_contract_address: &ContractAddress,
) -> ContractResult<()> {
    let is_operator = cis2_client::Cis2Client::is_operator_of(
        host,
        ctx.sender(),
        ctx.self_address(),
        cis_contract_address,
    )
    .map_err(MarketplaceError::Cis2ClientError)?;
    ensure!(is_operator, MarketplaceError::NotOperator);
    Ok(())
}
/// Calls the [balanceOf](https://proposals.concordium.software/CIS/cis-2.html#balanceof) function of the CIS2 contract.
/// Returns error if the returned balance < input balance (balance param).
fn ensure_balance<S: HasStateApi, T: IsTokenId + Copy, A: IsTokenAmount + Ord + Copy>(
    host: &mut impl HasHost<State<S, T, A>, StateApiType = S>,
    token_id: T,
    cis_contract_address: &ContractAddress,
    owner: AccountAddress,
    balance: A,
) -> ContractResult<()> {
    let contract_balance =
        Cis2Client::get_balance(host, token_id, cis_contract_address, Address::Account(owner))
            .map_err(MarketplaceError::Cis2ClientError)?;
    match contract_balance {
        Some(bal) => ensure!(bal.cmp(&balance).is_ge(), MarketplaceError::NoBalance),
        None => bail!(MarketplaceError::NoBalance),
    }

    Ok(())
}

// Distributes Selling Price, Royalty & Commission amounts.
fn distribute_amounts<S: HasStateApi, T: IsTokenId + Copy, A: IsTokenAmount + Copy>(
    host: &mut impl HasHost<State<S, T, A>, StateApiType = S>,
    amount: Amount,
    token_owner: &AccountAddress,
    token_royalty_state: &TokenRoyaltyState,
    marketplace_owner: &AccountAddress,
) -> Result<(), MarketplaceError> {
    let amounts = calculate_amounts(&amount, &host.state().commission, token_royalty_state.royalty);

    host.invoke_transfer(token_owner, amounts.to_seller)
        .map_err(|_| MarketplaceError::InvokeTransferError)?;

    if amounts.to_marketplace.cmp(&Amount::from_micro_ccd(0)).is_gt() {
        host.invoke_transfer(marketplace_owner, amounts.to_marketplace)
            .map_err(|_| MarketplaceError::InvokeTransferError)?;
    }

    if amounts.to_primary_owner.cmp(&Amount::from_micro_ccd(0)).is_gt() {
        host.invoke_transfer(&token_royalty_state.primary_owner, amounts.to_primary_owner)
            .map_err(|_| MarketplaceError::InvokeTransferError)?;
    };

    Ok(())
}

/// Calculates the amounts (Commission, Royalty & Selling Price) to be
/// distributed
fn calculate_amounts(
    amount: &Amount,
    commission: &Commission,
    royalty_percentage_basis: u16,
) -> DistributableAmounts {
    let commission_amount =
        (*amount * commission.percentage_basis.into()).quotient_remainder(MAX_BASIS_POINTS.into());

    let royalty_amount =
        (*amount * royalty_percentage_basis.into()).quotient_remainder(MAX_BASIS_POINTS.into());

    DistributableAmounts {
        to_seller:        amount
            .subtract_micro_ccd(commission_amount.0.micro_ccd())
            .subtract_micro_ccd(royalty_amount.0.micro_ccd()),
        to_marketplace:   commission_amount.0,
        to_primary_owner: royalty_amount.0,
    }
}

#[concordium_cfg_test]
mod test {
    use crate::{
        add, calculate_amounts,
        cis2_client::{
            BALANCE_OF_ENTRYPOINT_NAME, OPERATOR_OF_ENTRYPOINT_NAME, SUPPORTS_ENTRYPOINT_NAME,
        },
        list,
        params::AddParams,
        state::{Commission, State, TokenInfo, TokenListItem, TokenPriceState, TokenRoyaltyState},
        ContractState, ContractTokenAmount, ContractTokenId,
    };
    use concordium_cis2::*;

    use concordium_std::{test_infrastructure::*, *};

    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const CIS_CONTRACT_ADDRESS: ContractAddress = ContractAddress {
        index:    1,
        subindex: 0,
    };
    const MARKET_CONTRACT_ADDRESS: ContractAddress = ContractAddress {
        index:    2,
        subindex: 0,
    };

    #[concordium_test]
    fn should_add_token() {
        let token_id_1 = ContractTokenId::from(1);
        let token_quantity_1 = ContractTokenAmount::from(1);
        let price = Amount::from_ccd(1);

        let mut ctx = TestReceiveContext::default();
        ctx.set_sender(ADDRESS_0);
        ctx.set_self_address(MARKET_CONTRACT_ADDRESS);

        let add_params = AddParams {
            cis_contract_address: CIS_CONTRACT_ADDRESS,
            price,
            token_id: token_id_1,
            royalty: 0,
            quantity: token_quantity_1,
        };
        let parameter_bytes = to_bytes(&add_params);
        ctx.set_parameter(&parameter_bytes);

        let mut state_builder = TestStateBuilder::new();
        let state = State::new(&mut state_builder, 250);
        let mut host = TestHost::new(state, state_builder);

        fn mock_supports(
            _p: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut ContractState<TestStateApi>,
        ) -> Result<(bool, SupportsQueryResponse), CallContractError<SupportsQueryResponse>>
        {
            Ok((false, SupportsQueryResponse {
                results: vec![SupportResult::Support],
            }))
        }

        fn mock_is_operator_of(
            _p: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut ContractState<TestStateApi>,
        ) -> Result<(bool, OperatorOfQueryResponse), CallContractError<OperatorOfQueryResponse>>
        {
            Ok((false, OperatorOfQueryResponse {
                0: vec![true],
            }))
        }

        fn mock_balance_of(
            _p: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut ContractState<TestStateApi>,
        ) -> Result<
            (bool, BalanceOfQueryResponse<ContractTokenAmount>),
            CallContractError<BalanceOfQueryResponse<ContractTokenAmount>>,
        > {
            Ok((false, BalanceOfQueryResponse(vec![1.into()])))
        }

        TestHost::setup_mock_entrypoint(
            &mut host,
            CIS_CONTRACT_ADDRESS,
            OwnedEntrypointName::new_unchecked(SUPPORTS_ENTRYPOINT_NAME.to_string()),
            MockFn::new_v1(mock_supports),
        );

        TestHost::setup_mock_entrypoint(
            &mut host,
            CIS_CONTRACT_ADDRESS,
            OwnedEntrypointName::new_unchecked(OPERATOR_OF_ENTRYPOINT_NAME.to_string()),
            MockFn::new_v1(mock_is_operator_of),
        );

        TestHost::setup_mock_entrypoint(
            &mut host,
            CIS_CONTRACT_ADDRESS,
            OwnedEntrypointName::new_unchecked(BALANCE_OF_ENTRYPOINT_NAME.to_string()),
            MockFn::new_v1(mock_balance_of),
        );

        let res = add(&ctx, &mut host);

        claim!(res.is_ok(), "Results in rejection");
        claim!(host.state().token_prices.iter().count() != 0, "Token not added");
        claim!(host.state().token_royalties.iter().count() != 0, "Token not added");
        claim_eq!(host.state().commission, Commission {
            percentage_basis: 250,
        });

        let token_list_tuple = host
            .state()
            .get_listed(
                &TokenInfo {
                    id:      token_id_1,
                    address: CIS_CONTRACT_ADDRESS,
                },
                &ACCOUNT_0,
            )
            .expect("Should not be None");

        claim_eq!(token_list_tuple.0.to_owned(), TokenRoyaltyState {
            primary_owner: ACCOUNT_0,
            royalty:       0,
        });
        claim_eq!(token_list_tuple.1.to_owned(), TokenPriceState {
            price,
            quantity: token_quantity_1
        },)
    }

    #[concordium_test]
    fn should_list_token() {
        let token_quantity_1 = ContractTokenAmount::from(1);
        let token_id_1 = ContractTokenId::from(1);
        let token_id_2 = ContractTokenId::from(2);
        let token_price_1 = Amount::from_ccd(1);
        let token_price_2 = Amount::from_ccd(2);

        let mut ctx = TestReceiveContext::default();
        ctx.set_sender(ADDRESS_0);
        ctx.set_self_address(MARKET_CONTRACT_ADDRESS);

        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder, 250);
        state.list_token(
            &TokenInfo {
                id:      token_id_1,
                address: CIS_CONTRACT_ADDRESS,
            },
            &ACCOUNT_0,
            token_price_1,
            0,
            token_quantity_1,
        );
        state.list_token(
            &TokenInfo {
                id:      token_id_2,
                address: CIS_CONTRACT_ADDRESS,
            },
            &ACCOUNT_0,
            token_price_2,
            0,
            token_quantity_1,
        );
        let host = TestHost::new(state, state_builder);
        let list_result = list(&ctx, &host);

        claim!(list_result.is_ok());
        let token_list = list_result.unwrap();
        let list = token_list.0;
        claim_eq!(list.len(), 2);

        let first_token = list.first().unwrap();
        let second_token = list.last().unwrap();

        claim_eq!(first_token, &TokenListItem {
            token_id:      token_id_1,
            contract:      CIS_CONTRACT_ADDRESS,
            price:         token_price_1,
            owner:         ACCOUNT_0,
            primary_owner: ACCOUNT_0,
            quantity:      token_quantity_1,
            royalty:       0,
        });

        claim_eq!(second_token, &TokenListItem {
            token_id:      token_id_2,
            contract:      CIS_CONTRACT_ADDRESS,
            price:         token_price_2,
            owner:         ACCOUNT_0,
            primary_owner: ACCOUNT_0,
            quantity:      token_quantity_1,
            royalty:       0,
        })
    }

    #[concordium_test]
    fn calculate_commissions_test() {
        let commission_percentage_basis: u16 = 250;
        let royalty_percentage_basis: u16 = 1000;
        let init_amount = Amount::from_ccd(11);
        let distributable_amounts = calculate_amounts(
            &init_amount,
            &Commission {
                percentage_basis: commission_percentage_basis,
            },
            royalty_percentage_basis,
        );

        claim_eq!(distributable_amounts.to_seller, Amount::from_micro_ccd(9625000));
        claim_eq!(distributable_amounts.to_marketplace, Amount::from_micro_ccd(275000));
        claim_eq!(distributable_amounts.to_primary_owner, Amount::from_micro_ccd(1100000));
        claim_eq!(
            init_amount,
            Amount::from_ccd(0)
                .add_micro_ccd(distributable_amounts.to_seller.micro_ccd())
                .add_micro_ccd(distributable_amounts.to_marketplace.micro_ccd())
                .add_micro_ccd(distributable_amounts.to_primary_owner.micro_ccd())
        )
    }
}
