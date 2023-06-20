//! CIS2 client is the intermediatory layer between any contract and
//! CIS2 comliant contract.
//!
//! # Description
//! It allows the contract to abstract away the logic of calling the
//! CIS2 contract for the following methods
//! - `supports_cis2` : Calls [`supports`](https://proposals.concordium.software/CIS/cis-0.html#supports)
//! - `operator_of` : Calls [`operatorOf`](https://proposals.concordium.software/CIS/cis-2.html#operatorof)
//! - `balance_of` : Calls [`balanceOf`](https://proposals.concordium.software/CIS/cis-2.html#balanceof)
//! - `transfer` : Calls [`transfer`](https://proposals.concordium.software/CIS/cis-2.html#transfer)

use concordium_std::*;

use crate::*;

const CIS2_STANDARD_IDENTIFIER_STR: &str = "CIS-2";
const SUPPORTS_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("supports");
const OPERATOR_OF_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("operatorOf");
const BALANCE_OF_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("balanceOf");
const TRANSFER_ENTRYPOINT_NAME: EntrypointName = EntrypointName::new_unchecked("transfer");

/// Errors which can be returned by the `Cis2Client`.
#[derive(Serialize, Debug, PartialEq, Eq, Reject)]
pub enum Cis2ClientError {
    /// When there is an error invoking the CIS2 contract.
    InvokeContractError,
    /// When there is an error parsing the parameters.
    ParseParams,
    /// When there is an error parsing the result.
    ParseResult,
}

impl<T> From<CallContractError<T>> for Cis2ClientError {
    fn from(_: CallContractError<T>) -> Self { Cis2ClientError::InvokeContractError }
}

impl From<ParseError> for Cis2ClientError {
    fn from(_: ParseError) -> Self { Cis2ClientError::ParseParams }
}

pub struct Cis2Client;

impl Cis2Client {
    // calls the `supports` entrypoint of the CIS2 contract to check if the given
    // contract supports CIS2 standard. If the contract supports CIS2 standard,
    // it returns the contract address, else it returns None.
    pub fn supports_cis2<State, S: HasStateApi>(
        host: &mut impl HasHost<State, StateApiType = S>,
        cis_contract_address: &ContractAddress,
    ) -> Result<Option<ContractAddress>, Cis2ClientError> {
        let params = SupportsQueryParams {
            queries: vec![StandardIdentifierOwned::new_unchecked(
                CIS2_STANDARD_IDENTIFIER_STR.to_string(),
            )],
        };

        let parsed_res = match host.invoke_contract_read_only(
            cis_contract_address,
            &params,
            SUPPORTS_ENTRYPOINT_NAME,
            Amount::from_ccd(0),
        )? {
            // Since the contract should return a response. If it doesn't, it is an error.
            None => bail!(Cis2ClientError::InvokeContractError),
            Some(mut res) => SupportsQueryResponse::deserial(&mut res)?,
        };

        let supports_cis2 = parsed_res
            .results
            .first()
            .map(|f| match f {
                SupportResult::NoSupport => Option::None,
                SupportResult::Support => Option::Some(cis_contract_address),
                SupportResult::SupportBy(contracts) => contracts.first(),
            })
            .ok_or(Cis2ClientError::InvokeContractError)?;

        Ok(supports_cis2.copied())
    }

    // calls the `operatorOf` entrypoint of the CIS2 contract to check if the given
    // owner is an operator of the given contract. If the owner is an operator
    // of the given contract, it returns true, else it returns false.
    pub fn operator_of<State, S: HasStateApi>(
        host: &mut impl HasHost<State, StateApiType = S>,
        cis_contract_address: &ContractAddress,
        owner: Address,
        address: Address,
    ) -> Result<bool, Cis2ClientError> {
        let params = &OperatorOfQueryParams {
            queries: vec![OperatorOfQuery {
                owner,
                address,
            }],
        };

        let is_operators = match host.invoke_contract_read_only(
            cis_contract_address,
            params,
            OPERATOR_OF_ENTRYPOINT_NAME,
            Amount::from_ccd(0),
        )? {
            // Since the contract should return a response. If it doesn't, it is an error.
            None => bail!(Cis2ClientError::InvokeContractError),
            Some(mut res) => OperatorOfQueryResponse::deserial(&mut res)?,
        };

        // If the contract returns a response, but the response is empty, it is an
        // error. Since for a single query the response should be non-empty.
        let is_operator = *is_operators.0.first().ok_or(Cis2ClientError::InvokeContractError)?;

        Ok(is_operator)
    }

    // calls the `balanceOf` entrypoint of the CIS2 contract to get the balance of
    // the given owner for the given token. Returns the balance of the owner for
    // the given token.
    pub fn balance_of<State, S: HasStateApi, T: IsTokenId, A: IsTokenAmount + Copy>(
        host: &mut impl HasHost<State, StateApiType = S>,
        cis_contract_address: &ContractAddress,
        token_id: T,
        address: Address,
    ) -> Result<A, Cis2ClientError> {
        let params = BalanceOfQueryParams {
            queries: vec![BalanceOfQuery {
                token_id,
                address,
            }],
        };

        let balances: BalanceOfQueryResponse<A> = match host.invoke_contract_read_only(
            cis_contract_address,
            &params,
            BALANCE_OF_ENTRYPOINT_NAME,
            Amount::from_ccd(0),
        )? {
            // Since the contract should return a response. If it doesn't, it is an error.
            None => bail!(Cis2ClientError::InvokeContractError),
            Some(mut res) => BalanceOfQueryResponse::<A>::deserial(&mut res)?,
        };

        // If the contract returns a response, but the response is empty, it is an
        // error. Since for a single query the response should be non-empty.
        let balance = *balances.0.first().ok_or(Cis2ClientError::InvokeContractError)?;

        Ok(balance)
    }

    // calls the `transfer` entrypoint of the CIS2 contract to transfer the given
    // amount of tokens from the given owner to the given receiver.
    // If the transfer is successful, it returns `Ok(())`, else it returns an `Err`.
    pub fn transfer<State, S: HasStateApi, T: IsTokenId, A: IsTokenAmount + Copy>(
        host: &mut impl HasHost<State, StateApiType = S>,
        cis_contract_address: &ContractAddress,
        token_id: T,
        amount: A,
        from: Address,
        to: Receiver,
    ) -> Result<(), Cis2ClientError> {
        let params = TransferParams(vec![Transfer {
            token_id,
            amount,
            from,
            to,
            data: AdditionalData::empty(),
        }]);

        host.invoke_contract(
            cis_contract_address,
            &params,
            TRANSFER_ENTRYPOINT_NAME,
            Amount::from_ccd(0),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use concordium_std::{test_infrastructure::*, *};

    use crate::{cis2_client::Cis2ClientError, *};

    use super::Cis2Client;

    #[derive(Serial, Deserial, Clone)]
    pub struct TestState;

    const INDEX: u64 = 0;
    const SUBINDEX: u64 = 0;
    type ContractTokenId = TokenIdU8;
    type ContractTokenAmount = TokenAmountU8;

    #[test]
    fn supports_cis2_test_support() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        fn mock_supports(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
        ) -> Result<(bool, SupportsQueryResponse), CallContractError<SupportsQueryResponse>>
        {
            // Check that parameters are deserialized correctly.
            let mut cursor = Cursor::new(parameter);
            let params: Result<SupportsQueryParams, ParseError> =
                SupportsQueryParams::deserial(&mut cursor);
            assert!(params.is_ok());
            let params = params.unwrap();
            assert_eq!(
                params.queries[0],
                StandardIdentifierOwned::new_unchecked("CIS-2".to_owned())
            );

            // Return a response with support.
            Ok((false, SupportsQueryResponse {
                results: vec![SupportResult::Support],
            }))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("supports".to_string()),
            MockFn::new_v1(mock_supports),
        );

        let res = Cis2Client::supports_cis2(&mut host, &cis_contract_address);
        assert_eq!(res.unwrap(), Some(cis_contract_address));
    }

    #[test]
    fn supports_cis2_test_no_support() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        fn mock_supports(
            _p: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
        ) -> Result<(bool, SupportsQueryResponse), CallContractError<SupportsQueryResponse>>
        {
            Ok((false, SupportsQueryResponse {
                results: vec![SupportResult::NoSupport],
            }))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("supports".to_string()),
            MockFn::new_v1(mock_supports),
        );

        let res = Cis2Client::supports_cis2(&mut host, &cis_contract_address);
        assert_eq!(res.unwrap(), None);
    }

    #[test]
    fn supports_cis2_test_supported_by_other_contract() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        fn mock_supports(
            _p: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
        ) -> Result<(bool, SupportsQueryResponse), CallContractError<SupportsQueryResponse>>
        {
            Ok((false, SupportsQueryResponse {
                results: vec![SupportResult::SupportBy(vec![ContractAddress::new(
                    INDEX,
                    SUBINDEX + 1,
                )])],
            }))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("supports".to_string()),
            MockFn::new_v1(mock_supports),
        );

        let res = Cis2Client::supports_cis2(&mut host, &cis_contract_address);
        assert_eq!(res.unwrap(), Some(ContractAddress::new(INDEX, SUBINDEX + 1)));
    }

    #[test]
    fn operator_of_test() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        let owner = Address::Account(AccountAddress([1; 32]));
        let current_contract_address = Address::Contract(ContractAddress::new(INDEX + 1, SUBINDEX));
        fn mock_operator_of(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
        ) -> Result<(bool, OperatorOfQueryResponse), CallContractError<OperatorOfQueryResponse>>
        {
            // Check that parameters are deserialized correctly.
            let mut cursor = Cursor::new(parameter);
            let params: Result<OperatorOfQueryParams, ParseError> =
                OperatorOfQueryParams::deserial(&mut cursor);
            assert!(params.is_ok());
            let params = params.unwrap();
            assert_eq!(
                params.queries[0].address,
                Address::Contract(ContractAddress::new(INDEX + 1, SUBINDEX))
            );
            assert_eq!(params.queries[0].owner, Address::Account(AccountAddress([1; 32])));

            // Return a response with operator true.
            Ok((false, OperatorOfQueryResponse {
                0: vec![true],
            }))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("operatorOf".to_string()),
            MockFn::new_v1(mock_operator_of),
        );

        let res = Cis2Client::operator_of(
            &mut host,
            &cis_contract_address,
            owner,
            current_contract_address,
        );

        assert_eq!(res.unwrap(), true);
    }

    #[test]
    fn balance_of_test() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        let owner = Address::Account(AccountAddress([1; 32]));
        fn mock_balance_of(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
        ) -> Result<
            (bool, BalanceOfQueryResponse<ContractTokenAmount>),
            CallContractError<BalanceOfQueryResponse<ContractTokenAmount>>,
        > {
            // Check that parameters are deserialized correctly.
            let mut cursor = Cursor::new(parameter);
            let params: Result<BalanceOfQueryParams<ContractTokenId>, ParseError> =
                BalanceOfQueryParams::deserial(&mut cursor);
            assert!(params.is_ok());
            let params = params.unwrap();
            assert_eq!(params.queries[0].token_id, TokenIdU8(1));
            assert_eq!(params.queries[0].address, Address::Account(AccountAddress([1; 32])));

            // Return a balance of 1.
            Ok((false, BalanceOfQueryResponse(vec![1.into()])))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("balanceOf".to_string()),
            MockFn::new_v1(mock_balance_of),
        );

        let res: Result<ContractTokenAmount, Cis2ClientError> =
            Cis2Client::balance_of(&mut host, &cis_contract_address, TokenIdU8(1), owner);

        assert!(res.is_ok());
        let res = res.unwrap();
        assert_eq!(res, 1.into());
    }

    #[test]
    fn transfer_test() {
        let state = TestState {};
        let state_builder = TestStateBuilder::new();
        let mut host = TestHost::new(state, state_builder);
        let cis_contract_address = ContractAddress::new(INDEX, SUBINDEX);
        let from = Address::Account(AccountAddress([1; 32]));
        let to_account = AccountAddress([2; 32]);
        let amount: ContractTokenAmount = 1.into();

        fn mock_transfer(
            parameter: Parameter,
            _a: Amount,
            _a2: &mut Amount,
            _s: &mut TestState,
        ) -> Result<(bool, ()), CallContractError<()>> {
            // Check that parameters are deserialized correctly.
            let mut cursor = Cursor::new(parameter);
            let params: Result<TransferParams<ContractTokenId, ContractTokenAmount>, ParseError> =
                TransferParams::deserial(&mut cursor);
            assert!(params.is_ok());
            let params = params.unwrap();
            assert_eq!(params.0[0].token_id, TokenIdU8(1));
            assert_eq!(params.0[0].to.address(), Address::Account(AccountAddress([2; 32])));
            assert_eq!(params.0[0].amount, 1.into());

            // Return a successful transfer.
            Ok((false, ()))
        }

        host.setup_mock_entrypoint(
            cis_contract_address,
            OwnedEntrypointName::new_unchecked("transfer".to_string()),
            MockFn::new_v1(mock_transfer),
        );

        let res: Result<(), Cis2ClientError> = Cis2Client::transfer(
            &mut host,
            &cis_contract_address,
            TokenIdU8(1),
            amount,
            from,
            Receiver::Account(to_account),
        );

        assert!(res.is_ok());
    }
}
