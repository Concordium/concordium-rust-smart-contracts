//! Tests for the `nametoken` contract.
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std_derive::*;
use nametoken::*;

/// The tests accounts.
const ALICE: AccountAddress =
    account_address!("2wkBET2rRgE8pahuaczxKbmv7ciehqsne57F9gtzf1PVdr2VP3");
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = account_address!("2xBpaHottqhwFZURMZW4uZduQvpxNDSy46iXMYs9kceNGaPpZX");
const BOB_ADDR: Address = Address::Account(BOB);
const CHARLIE: AccountAddress =
    account_address!("2xdTv8awN1BjgYEw8W1BVXVtiEwG2b29U8KoZQqJrDuEqddseE");

/// Token IDs.
const NAME_0: &str = "MyEvenCoolerName";
const NAME_0_TOKEN_ID: ContractTokenId = TokenIdFixed([
    24, 188, 23, 153, 239, 160, 1, 1, 235, 169, 225, 59, 20, 47, 103, 115, 3, 188, 0, 164, 87, 161,
    21, 92, 67, 206, 126, 235, 0, 101, 54, 231,
]);
const NAME_1: &str = "MyCoolName";
const NAME_1_TOKEN_ID: ContractTokenId = TokenIdFixed([
    183, 115, 55, 205, 199, 72, 252, 206, 49, 209, 119, 201, 194, 140, 103, 91, 216, 188, 175, 84,
    169, 226, 17, 22, 227, 62, 16, 117, 35, 207, 236, 137,
]);
const SAMPLE_DATA: &str = "GitHub: my-github-name";

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

/// A signer for all the transactions.
const SIGNER: Signer = Signer::with_one_key();

/// Timestamps.
const YEAR: u64 = 365 * 24 * 60 * 60 * 1000;
const DAY: u64 = 24 * 60 * 60 * 1000;
const YEAR_ONE: Timestamp = Timestamp::from_timestamp_millis(YEAR);
const YEAR_TWO: Timestamp = Timestamp::from_timestamp_millis(YEAR + YEAR);
const YEAR_TWO_PLUS_DAY: Timestamp = Timestamp::from_timestamp_millis(YEAR + YEAR + DAY);

/// Test that registering a fresh name works.
#[test]
fn test_register_fresh() {
    // Initialize the chain and contract. Also register two names for Alice.
    let (chain, contract_address, update) = initialize_contract_with_alice_names();

    // Invoke the view entrypoint.
    let view = invoke_view(&chain, contract_address);

    // Check that Alice owns the two names `NAME_0` and `NAME_1`.
    assert_eq!(
        view,
        ViewState {
            state: vec![(
                ALICE,
                ViewAddressState {
                    owned_names: vec![NAME_0_TOKEN_ID, NAME_1_TOKEN_ID],
                    operators: Vec::new(),
                }
            )],
            all_names: vec![
                (
                    NAME_0_TOKEN_ID,
                    ViewNameInfo {
                        name_expires: YEAR_ONE,
                        owner: ALICE,
                        data: Vec::new(),
                    }
                ),
                (
                    NAME_1_TOKEN_ID,
                    ViewNameInfo {
                        name_expires: YEAR_ONE,
                        owner: ALICE,
                        data: Vec::new(),
                    }
                )
            ],
        }
    );

    // Check that a mint and tokenmetadata event was emitted.
    // Since `initialize_contract_with_alice_names` only returns the update for the
    // second registration, that is what we check.
    let events = deserialize_update_events(&update);
    assert_eq!(
        events,
        [
            Cis2Event::Mint(MintEvent {
                token_id: NAME_1_TOKEN_ID,
                amount: 1.into(),
                owner: ALICE_ADDR,
            }),
            Cis2Event::TokenMetadata(TokenMetadataEvent {
                token_id: NAME_1_TOKEN_ID,
                metadata_url: MetadataUrl {
                    url: build_token_metadata_url(&NAME_1_TOKEN_ID),
                    hash: None,
                },
            }),
        ]
    );
}

/// Test registering an expired name.
#[test]
fn test_register_expired() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Add some data to `TOKEN_0`, so that we can check that it is cleared on
    // re-registration.
    update_data(&mut chain, contract_address, NAME_0, SAMPLE_DATA).expect("Update data");

    // Advance time by 366 days, i.e. beyond the expiration date of the name.
    chain
        .tick_block_time(Duration::from_days(366))
        .expect("Time doesn't overflow.");

    // Register `NAME_0` with Bob as the owner.
    let parameter = RegisterNameParams {
        name: NAME_0.to_string(),
        owner: BOB,
    };
    let update = chain
        .contract_update(
            SIGNER,
            BOB,
            BOB_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: REGISTRATION_FEE,
                receive_name: OwnedReceiveName::new_unchecked("NameToken.register".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Register name params"),
            },
        )
        .expect("Register NAME_0");

    // Check that the name is now owned by Bob and has no data.
    // Also check that the `NAME_1` is now expired.
    let view = invoke_view(&chain, contract_address);
    assert_eq!(
        view.all_names,
        vec![
            (
                NAME_0_TOKEN_ID,
                ViewNameInfo {
                    name_expires: YEAR_TWO_PLUS_DAY, // <- New expiration date.
                    owner: BOB,
                    data: Vec::new(), // <- No data.
                }
            ),
            (
                NAME_1_TOKEN_ID,
                ViewNameInfo {
                    name_expires: YEAR_ONE, // <- Expired.
                    owner: ALICE,
                    data: Vec::new(),
                }
            )
        ]
    );

    // Check that a trasnfer event was produced, tranferring `NAME_0` from Alice to
    // Bob.
    let events = deserialize_update_events(&update);
    assert_eq!(
        events,
        [Cis2Event::Transfer(TransferEvent {
            token_id: NAME_0_TOKEN_ID,
            from: ALICE_ADDR,
            to: BOB_ADDR,
            amount: 1.into(),
        }),]
    );
}

/// Test that registering fails if the fee is incorrect.
#[test]
fn test_register_fails_incorrect_fee() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Register `NAME_0` with Bob as the owner.
    let parameter = RegisterNameParams {
        name: NAME_0.to_string(),
        owner: BOB,
    };
    let update = chain
        .contract_update(
            SIGNER,
            BOB,
            BOB_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: REGISTRATION_FEE + Amount::from_micro_ccd(1), // Incorrect fee.
                receive_name: OwnedReceiveName::new_unchecked("NameToken.register".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Register name params"),
            },
        )
        .expect_err("Register NAME_0 with incorrect fee");

    // Check that it returns the correct error.
    let error: ContractError = update.parse_return_value().expect("Deserialize error");
    assert_eq!(
        error,
        ContractError::Custom(CustomContractError::IncorrectFee)
    );
}

/// Test transfer succeeds, when `from` is the sender.
#[test]
fn test_transfer_account() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Transfer `NAME_0` from Alice to Bob.
    let parameter: nametoken::TransferParameter = TransferParams(vec![concordium_cis2::Transfer {
        token_id: NAME_0_TOKEN_ID,
        amount: ContractTokenAmount::from(1),
        from: ALICE_ADDR,
        to: Receiver::from_account(BOB),
        data: AdditionalData::empty(),
    }]);

    let update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("NameToken.transfer".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Transfer name params"),
            },
        )
        .expect("Transfer NAME_0");

    // Check that name 0 is now owned by Bob, and that Alice still owns name 1.
    let view = invoke_view(&chain, contract_address);
    assert_eq!(
        view.all_names,
        vec![
            (
                NAME_0_TOKEN_ID,
                ViewNameInfo {
                    name_expires: YEAR_ONE,
                    owner: BOB,
                    data: Vec::new(),
                }
            ),
            (
                NAME_1_TOKEN_ID,
                ViewNameInfo {
                    name_expires: YEAR_ONE,
                    owner: ALICE,
                    data: Vec::new(),
                }
            )
        ]
    );

    // Check that a trasnfer event was produced, tranferring `NAME_0` from Alice to
    // Bob.
    let events = deserialize_update_events(&update);
    assert_eq!(
        events,
        [Cis2Event::Transfer(TransferEvent {
            token_id: NAME_0_TOKEN_ID,
            from: ALICE_ADDR,
            to: BOB_ADDR,
            amount: 1.into(),
        }),]
    );
}

/// Test that a transfer fails when the name is expired.
#[test]
fn test_transfer_expired_name_fails() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Advance time by 366 days, i.e. beyond the expiration date of the name.
    chain
        .tick_block_time(Duration::from_days(366))
        .expect("Time doesn't overflow.");

    // Transfer `NAME_0` from Alice to Bob.
    let parameter: nametoken::TransferParameter = TransferParams(vec![concordium_cis2::Transfer {
        token_id: NAME_0_TOKEN_ID,
        amount: ContractTokenAmount::from(1),
        from: ALICE_ADDR,
        to: Receiver::from_account(BOB),
        data: AdditionalData::empty(),
    }]);

    let update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("NameToken.transfer".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Transfer name params"),
            },
        )
        .expect_err("Transfer NAME_0");

    // Check that it returns the correct error.
    let error: ContractError = update.parse_return_value().expect("Deserialize error");
    assert_eq!(
        error,
        ContractError::Custom(CustomContractError::NameExpired)
    );
}

/// Test that adding an operator works and produces the correct events.
#[test]
fn test_add_operator() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Add Bob as an operator for Alice.
    let update_operator = add_bob_the_operator(&mut chain, contract_address);

    // Check that the operator was added.
    let view = invoke_view(&chain, contract_address);
    assert_eq!(
        view,
        ViewState {
            state: vec![(
                ALICE,
                ViewAddressState {
                    owned_names: vec![NAME_0_TOKEN_ID, NAME_1_TOKEN_ID],
                    operators: vec![BOB_ADDR], // Bob is now an operator.
                }
            )],
            all_names: vec![
                (
                    NAME_0_TOKEN_ID,
                    ViewNameInfo {
                        name_expires: YEAR_ONE,
                        owner: ALICE,
                        data: Vec::new(),
                    }
                ),
                (
                    NAME_1_TOKEN_ID,
                    ViewNameInfo {
                        name_expires: YEAR_ONE,
                        owner: ALICE,
                        data: Vec::new(),
                    }
                )
            ],
        }
    );

    // Check that an operator event was emitted.
    let events = deserialize_update_events(&update_operator);
    assert_eq!(
        events,
        [Cis2Event::UpdateOperator(UpdateOperatorEvent {
            owner: ALICE_ADDR,
            operator: BOB_ADDR,
            update: OperatorUpdate::Add,
        }),]
    );
}

/// Test that an operator can make a transfer on behalf of the owner.
#[test]
fn test_operator_transfer() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Add Bob as an operator for Alice.
    add_bob_the_operator(&mut chain, contract_address);

    // Transfer `NAME_0` from Alice to Charlie, using Bob as the operator.
    let parameter: nametoken::TransferParameter = TransferParams(vec![concordium_cis2::Transfer {
        token_id: NAME_0_TOKEN_ID,
        amount: ContractTokenAmount::from(1),
        from: ALICE_ADDR,
        to: Receiver::from_account(CHARLIE),
        data: AdditionalData::empty(),
    }]);
    chain
        .contract_update(
            SIGNER,
            BOB,
            BOB_ADDR, // Bob the operator sends it.
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("NameToken.transfer".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Transfer name params"),
            },
        )
        .expect("Transfer NAME_0");

    // Check the new balances.
    let view = invoke_view(&chain, contract_address);
    assert_eq!(
        view,
        ViewState {
            state: vec![
                (
                    ALICE,
                    ViewAddressState {
                        owned_names: vec![NAME_1_TOKEN_ID],
                        operators: vec![BOB_ADDR],
                    }
                ),
                (
                    CHARLIE,
                    ViewAddressState {
                        owned_names: vec![NAME_0_TOKEN_ID], // Charlie now owns name 0.
                        operators: Vec::new(),
                    }
                )
            ],
            all_names: vec![
                (
                    NAME_0_TOKEN_ID,
                    ViewNameInfo {
                        name_expires: YEAR_ONE,
                        owner: CHARLIE,
                        data: Vec::new(),
                    }
                ),
                (
                    NAME_1_TOKEN_ID,
                    ViewNameInfo {
                        name_expires: YEAR_ONE,
                        owner: ALICE,
                        data: Vec::new(),
                    }
                )
            ],
        }
    );
}

/// Test renewing an existing name.
#[test]
fn test_renew_name() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Renew `NAME_0`.
    let parameter = NAME_0.to_string();

    chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: RENEWAL_FEE, // Send renewal fee.
                receive_name: OwnedReceiveName::new_unchecked("NameToken.renewName".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Renew name params"),
            },
        )
        .expect("Renew NAME_0");

    // Check that the new expiration date is 1 year from now.
    let view = invoke_view(&chain, contract_address);
    assert_eq!(
        view.all_names,
        vec![
            (
                NAME_0_TOKEN_ID,
                ViewNameInfo {
                    name_expires: YEAR_TWO, // Now expires in two year.
                    owner: ALICE,
                    data: Vec::new(),
                }
            ),
            (
                NAME_1_TOKEN_ID,
                ViewNameInfo {
                    name_expires: YEAR_ONE,
                    owner: ALICE,
                    data: Vec::new(),
                }
            )
        ]
    );
}

/// Test that renewing a name fails if the name has expired.
#[test]
fn test_renew_expired_name_fails() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Advance time by 366 days, i.e. beyond the expiration date of the name.
    chain
        .tick_block_time(Duration::from_days(366))
        .expect("Time doesn't overflow.");

    // Renew `NAME_0`.
    let parameter = NAME_0.to_string();

    let update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: RENEWAL_FEE, // Send renewal fee.
                receive_name: OwnedReceiveName::new_unchecked("NameToken.renewName".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Renew name params"),
            },
        )
        .expect_err("Renew NAME_0");

    // Check that it returns the correct error.
    let error: ContractError = update.parse_return_value().expect("Deserialize error");
    assert_eq!(
        error,
        ContractError::Custom(CustomContractError::NameExpired)
    );
}

/// Test updating data for an existing name.
#[test]
fn test_update_data() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Update the data.
    update_data(&mut chain, contract_address, NAME_0, SAMPLE_DATA).expect("Update data");

    // Check that the data was updated.
    let view = invoke_view(&chain, contract_address);
    assert_eq!(
        view.all_names,
        vec![
            (
                NAME_0_TOKEN_ID,
                ViewNameInfo {
                    name_expires: YEAR_ONE,
                    owner: ALICE,
                    data: SAMPLE_DATA.as_bytes().to_owned(), // The new data.
                }
            ),
            (
                NAME_1_TOKEN_ID,
                ViewNameInfo {
                    name_expires: YEAR_ONE,
                    owner: ALICE,
                    data: Vec::new(),
                }
            )
        ]
    );
}

/// Test that updating the data on an expired name fails.
#[test]
fn test_update_data_on_expired_fails() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Advance time by 366 days, i.e. beyond the expiration date of the name.
    chain
        .tick_block_time(Duration::from_days(366))
        .expect("Time doesn't overflow.");

    // Update the data.
    let update = update_data(&mut chain, contract_address, NAME_0, SAMPLE_DATA)
        .expect_err("Update data on expired name");

    // Check that it returns the correct error.
    let error: ContractError = update.parse_return_value().expect("Deserialize error");
    assert_eq!(
        error,
        ContractError::Custom(CustomContractError::NameExpired)
    );
}

/// Test the nameinfo view.
#[test]
fn test_name_info_view() {
    let (chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Invoke the view entrypoint.
    let parameter = NAME_0.to_string();
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("NameToken.viewNameInfo".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Name info params"),
            },
        )
        .expect("Invoke view");

    // Check that the view returns the correct data.
    let view: ViewNameInfo = invoke.parse_return_value().expect("Deserialize view");
    assert_eq!(
        view,
        ViewNameInfo {
            name_expires: YEAR_ONE,
            owner: ALICE,
            data: Vec::new(),
        }
    );
}

/// Test querying balances for expired and unexpired names.
#[test]
fn test_balance_of_expired_not_expired() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // Renew `NAME_0`, so that it expires in year two.
    let parameter = NAME_0.to_string();
    chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: RENEWAL_FEE, // Send renewal fee.
                receive_name: OwnedReceiveName::new_unchecked("NameToken.renewName".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Renew name params"),
            },
        )
        .expect("Renew NAME_0");

    // Advance time by 366 days, i.e. beyond the expiration date of the name 1.
    chain
        .tick_block_time(Duration::from_days(366))
        .expect("Time doesn't overflow.");

    // Construct the balance of parameter.
    let parameter: ContractBalanceOfQueryParams = BalanceOfQueryParams {
        queries: vec![
            BalanceOfQuery {
                address: ALICE_ADDR,
                token_id: NAME_0_TOKEN_ID,
            },
            BalanceOfQuery {
                address: ALICE_ADDR,
                token_id: NAME_1_TOKEN_ID,
            },
        ],
    };

    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("NameToken.balanceOf".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Balance of params"),
            },
        )
        .expect("Invoke view");

    // Check that Alice now has one name 0, which is still valid, and zero of name
    // 1, which is expired.
    let response: ContractBalanceOfQueryResponse =
        invoke.parse_return_value().expect("Deserialize view");
    assert_eq!(
        response,
        BalanceOfQueryResponse(vec![
            ContractTokenAmount::from(1),
            ContractTokenAmount::from(0)
        ])
    );
}

/// Test that the admin can be updated.
#[test]
fn test_update_admin() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // The new admin is Charlie.
    let new_admin = CHARLIE;

    // Update the admin.
    chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("NameToken.updateAdmin".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&new_admin).expect("Update admin params"),
            },
        )
        .expect("Update admin");
}

/// Test that the admin can't be updated by a non-admin.
#[test]
fn test_update_admin_fails_unauthorized() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_names();

    // The new admin is Charlie.
    let new_admin = CHARLIE;

    // Update the admin.
    let update = chain
        .contract_update(
            SIGNER,
            BOB,
            BOB_ADDR, // Bob is not the admin.
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("NameToken.updateAdmin".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&new_admin).expect("Update admin params"),
            },
        )
        .expect_err("Update admin");

    // Check that it returns the correct error.
    let error: ContractError = update.parse_return_value().expect("Deserialize error");
    assert_eq!(error, ContractError::Unauthorized);
}

// Helpers:

/// Update the data of a name using the Alice account.
/// Returns the result.
fn update_data(
    chain: &mut Chain,
    contract_address: ContractAddress,
    name: &str,
    data: &str,
) -> Result<ContractInvokeSuccess, ContractInvokeError> {
    let parameter = UpdateDataParams {
        name: name.to_string(),
        data: data.as_bytes().to_owned(),
    };

    chain.contract_update(
        SIGNER,
        ALICE,
        ALICE_ADDR,
        Energy::from(10000),
        UpdateContractPayload {
            amount: UPDATE_FEE,
            receive_name: OwnedReceiveName::new_unchecked("NameToken.updateData".to_string()),
            address: contract_address,
            message: OwnedParameter::from_serial(&parameter).expect("Update name data params"),
        },
    )
}

/// Helper function that sets up the contract with two names owned by Alice,
/// `NAME_0` and `NAME_1`.
///
/// Returns the `ContractInvokeSuccess` for the `NAME_1` registration.
fn initialize_contract_with_alice_names() -> (Chain, ContractAddress, ContractInvokeSuccess) {
    let (mut chain, contract_address) = initialize_chain_and_contract();

    let parameter_0 = RegisterNameParams {
        name: NAME_0.to_string(),
        owner: ALICE,
    };

    // Register `NAME_0`.
    chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: REGISTRATION_FEE,
                receive_name: OwnedReceiveName::new_unchecked("NameToken.register".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter_0).expect("Register name params"),
            },
        )
        .expect("Register NAME_0");

    let parameter_1 = RegisterNameParams {
        name: NAME_1.to_string(),
        owner: ALICE,
    };

    // Register `NAME_1`.
    let update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: REGISTRATION_FEE,
                receive_name: OwnedReceiveName::new_unchecked("NameToken.register".to_string()),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter_1).expect("Register name params"),
            },
        )
        .expect("Register NAME_1");

    (chain, contract_address, update)
}

/// Invoke the view entrypoint and return its results.
fn invoke_view(chain: &Chain, contract_address: ContractAddress) -> ViewState {
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("NameToken.view".to_string()),
                address: contract_address,
                message: OwnedParameter::empty(),
            },
        )
        .expect("Invoke view");
    invoke.parse_return_value().expect("Deserialize ViewState")
}

/// Deserialize the events from an update.
fn deserialize_update_events(
    update: &ContractInvokeSuccess,
) -> Vec<Cis2Event<ContractTokenId, ContractTokenAmount>> {
    update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect()
}

/// Setup chain and contract.
///
/// Also creates the three accounts, Alice, Bob and Charlie.
///
/// Alice is the owner and admin of the contract.
fn initialize_chain_and_contract() -> (Chain, ContractAddress) {
    let mut chain = Chain::new();

    // Create some accounts on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(CHARLIE, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain
        .module_deploy_v1(SIGNER, ALICE, module)
        .expect("Deploy valid module");

    // Initialize the auction contract.
    let init = chain
        .contract_init(
            SIGNER,
            ALICE,
            Energy::from(10000),
            InitContractPayload {
                amount: Amount::zero(),
                mod_ref: deployment.module_reference,
                init_name: OwnedContractName::new_unchecked("init_NameToken".to_string()),
                param: OwnedParameter::empty(),
            },
        )
        .expect("Initialize contract");

    (chain, init.contract_address)
}

/// Helper function that adds BOB as an operator for ALICE.
/// Returns the `ContractInvokeSuccess` for the update.
fn add_bob_the_operator(
    chain: &mut Chain,
    contract_address: ContractAddress,
) -> ContractInvokeSuccess {
    let parameter = UpdateOperatorParams(vec![UpdateOperator {
        update: OperatorUpdate::Add,
        operator: BOB_ADDR,
    }]);

    chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "NameToken.updateOperator".to_string(),
                ),
                address: contract_address,
                message: OwnedParameter::from_serial(&parameter).expect("Update operator params"),
            },
        )
        .expect("Add Bob as operator")
}
