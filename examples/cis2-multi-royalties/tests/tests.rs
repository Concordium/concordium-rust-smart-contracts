//! Tests for the `cis2_multi_royalties` contract.
use cis2_multi_royalties::*;
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::collections::BTreeMap;
use concordium_std_derive::*;

/// The tests accounts.
const ALICE: AccountAddress = account_address!("2wkBET2rRgE8pahuaczxKbmv7ciehqsne57F9gtzf1PVdr2VP3");
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = account_address!("2xBpaHottqhwFZURMZW4uZduQvpxNDSy46iXMYs9kceNGaPpZX");
const BOB_ADDR: Address = Address::Account(BOB);
const CHARLIE: AccountAddress = account_address!("2xdTv8awN1BjgYEw8W1BVXVtiEwG2b29U8KoZQqJrDuEqddseE");
const CHARLIE_ADDR: Address = Address::Account(CHARLIE);

/// Token IDs.
const TOKEN_0: ContractTokenId = TokenIdU8(2);
const TOKEN_1: ContractTokenId = TokenIdU8(42);

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

/// A signer for all the transactions.
const SIGNER: Signer = Signer::with_one_key();

/// Test minting succeeds and the tokens are owned by the given address and
/// the appropriate events are logged.
#[test]
fn test_minting() {
    let (chain, contract_address, update) = initialize_contract_with_alice_tokens(0);

    // Invoke the view entrypoint and check that the tokens are owned by Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi_royalties.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");

    // Check that the tokens are owned by Alice.
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.tokens[..], [TOKEN_0, TOKEN_1]);
    assert_eq!(rv.state, vec![(ALICE_ADDR, ViewAddressState {
        balances:  vec![(TOKEN_0, 400.into()), (TOKEN_1, 1.into())],
        operators: Vec::new(),
    })]);

    // Check that the events are logged.
    let events = update.events().flat_map(|(_addr, events)| events);

    let events: Vec<Cis2Event<ContractTokenId, ContractTokenAmount>> =
        events.map(|e| e.parse().expect("Deserialize event")).collect();

    assert_eq!(events, [
        Cis2Event::Mint(MintEvent {
            token_id: TokenIdU8(2),
            amount:   TokenAmountU64(400),
            owner:    ALICE_ADDR,
        }),
        Cis2Event::TokenMetadata(TokenMetadataEvent {
            token_id:     TokenIdU8(2),
            metadata_url: MetadataUrl {
                url:  "https://some.example/token/02".to_string(),
                hash: None,
            },
        }),
        Cis2Event::Mint(MintEvent {
            token_id: TokenIdU8(42),
            amount:   TokenAmountU64(1),
            owner:    ALICE_ADDR,
        }),
        Cis2Event::TokenMetadata(TokenMetadataEvent {
            token_id:     TokenIdU8(42),
            metadata_url: MetadataUrl {
                url:  "https://some.example/token/2A".to_string(),
                hash: None,
            },
        }),
    ]);
}

/// Test regular transfer where sender is the owner.
#[test]
fn test_account_transfer() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens(0);

    // Transfer one token from Alice to Bob.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(1),
        data:     AdditionalData::empty(),
    }]);

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_royalties.transfer".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Bob has 1 `TOKEN_0` and Alice has 399. Also check that Alice still
    // has 1 `TOKEN_1`.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi_royalties.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.state, vec![
        (ALICE_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 399.into()), (TOKEN_1, 1.into())],
            operators: Vec::new(),
        }),
        (BOB_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 1.into())],
            operators: Vec::new(),
        }),
    ]);

    // Check that the events are logged.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Cis2Event<_, _>>>();

    // Check that two events are produced, since royalties are enabled.
    // One, which transfers 0% of the cost to the royalty receiver (i.e., the
    // original minter, which is Alice). And another, which transfers the
    // remaininng 100% to the receiver (i.e., Bob).
    assert_eq!(events, [
        Cis2Event::Transfer(TransferEvent {
            token_id: TOKEN_0,
            amount:   TokenAmountU64(0), // Royalties paid to Alice.
            from:     ALICE_ADDR,
            to:       ALICE_ADDR,
        }),
        Cis2Event::Transfer(TransferEvent {
            token_id: TOKEN_0,
            amount:   TokenAmountU64(1), // Transfer made to Bob.
            from:     ALICE_ADDR,
            to:       BOB_ADDR,
        }),
    ]);
}

/// Test that you can add an operator.
/// Initialize the contract with two tokens owned by Alice.
/// Then add Bob as an operator for Alice.
#[test]
fn test_add_operator() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens(0);

    // Add Bob as an operator for Alice.
    let params = UpdateOperatorParams(vec![UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    }]);

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_royalties.updateOperator".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&params).expect("UpdateOperator params"),
        })
        .expect("Update operator");

    // Check that an operator event occurred.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Cis2Event<ContractTokenId, ContractTokenAmount>>>();
    assert_eq!(events, [Cis2Event::UpdateOperator(UpdateOperatorEvent {
        operator: BOB_ADDR,
        owner:    ALICE_ADDR,
        update:   OperatorUpdate::Add,
    }),]);

    // Construct a query parameter to check whether Bob is an operator for Alice.
    let query_params = OperatorOfQueryParams {
        queries: vec![OperatorOfQuery {
            owner:   ALICE_ADDR,
            address: BOB_ADDR,
        }],
    };

    // Invoke the operatorOf view entrypoint and check that Bob is an operator for
    // Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_royalties.operatorOf".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&query_params).expect("OperatorOf params"),
        })
        .expect("Invoke view");

    let rv: OperatorOfQueryResponse = invoke.parse_return_value().expect("OperatorOf return value");
    assert_eq!(rv, OperatorOfQueryResponse(vec![true]));
}

/// Test that a transfer fails when the sender is neither an operator or the
/// owner. In particular, Bob will attempt to transfer some of Alice's tokens to
/// himself.
#[test]
fn test_unauthorized_sender() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens(0);

    // Construct a transfer of `TOKEN_0` from Alice to Bob, which will be submitted
    // by Bob.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(1),
        data:     AdditionalData::empty(),
    }]);

    // Notice that Bob is the sender/invoker.
    let update = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_royalties.transfer".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect_err("Transfer tokens");

    // Check that the correct error is returned.
    let rv: ContractError = update.parse_return_value().expect("ContractError return value");
    assert_eq!(rv, ContractError::Unauthorized);
}

/// Test that an operator can make a transfer.
#[test]
fn test_operator_can_transfer() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens(0);

    // Add Bob as an operator for Alice.
    let params = UpdateOperatorParams(vec![UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    }]);
    chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_royalties.updateOperator".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&params).expect("UpdateOperator params"),
        })
        .expect("Update operator");

    // Let Bob make a transfer to himself on behalf of Alice.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(1),
        data:     AdditionalData::empty(),
    }]);

    chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_royalties.transfer".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Bob now has 1 of `TOKEN_0` and Alice has 399. Also check that
    // Alice still has 1 `TOKEN_1`.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi_royalties.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.state, vec![
        (ALICE_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 399.into()), (TOKEN_1, 1.into())],
            operators: vec![BOB_ADDR],
        }),
        (BOB_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 1.into())],
            operators: Vec::new(),
        }),
    ]);
}

/// Test that royalties are paid out correctly.
/// Set the royalty percentage to 50%.
#[test]
fn test_royalty_payment() {
    // Set the royalty percentage to 50%.
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens(50);

    // Transfer 100 `TOKEN_0` from Alice to Bob.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(100),
        data:     AdditionalData::empty(),
    }]);

    let update_1 = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_royalties.transfer".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Alice now has 350 tokens and Bob has 50, since 50 of them were
    // paid in royalties to Alice.
    let invoke_1 = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi_royalties.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");
    let rv: ViewState = invoke_1.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.state, vec![
        (ALICE_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 350.into()), (TOKEN_1, 1.into())],
            operators: Vec::new(),
        }),
        (BOB_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 50.into())],
            operators: Vec::new(),
        }),
    ]);

    // Check that two transfer events were logged.
    let events = update_1
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Cis2Event<_, _>>>();
    assert_eq!(events, [
        Cis2Event::Transfer(TransferEvent {
            token_id: TOKEN_0,
            amount:   TokenAmountU64(50), // Royalties paid to Alice.
            from:     ALICE_ADDR,
            to:       ALICE_ADDR,
        }),
        Cis2Event::Transfer(TransferEvent {
            token_id: TOKEN_0,
            amount:   TokenAmountU64(50), // Transfer made to Bob.
            from:     ALICE_ADDR,
            to:       BOB_ADDR,
        }),
    ]);

    // Transfer 50 `TOKEN_0` from Bob to Charlie.
    let transfer_params_2 = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     BOB_ADDR,
        to:       Receiver::Account(CHARLIE),
        token_id: TOKEN_0,
        amount:   TokenAmountU64(50),
        data:     AdditionalData::empty(),
    }]);
    let update_2 = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_multi_royalties.transfer".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params_2).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Bob now has 0 tokens and Charlie has 25, since 25 of them were
    // paid in royalties to Alice, who now has 375.
    let invoke_2 = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi_royalties.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");
    let rv: ViewState = invoke_2.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.state, vec![
        (ALICE_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 375.into()), (TOKEN_1, 1.into())],
            operators: Vec::new(),
        }),
        (BOB_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 0.into())],
            operators: Vec::new(),
        }),
        (CHARLIE_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 25.into())],
            operators: Vec::new(),
        }),
    ]);

    // Check that two transfer events were logged.
    let events = update_2
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Cis2Event<_, _>>>();
    assert_eq!(events, [
        Cis2Event::Transfer(TransferEvent {
            token_id: TOKEN_0,
            amount:   TokenAmountU64(25), // Royalties paid to Alice.
            from:     BOB_ADDR,
            to:       ALICE_ADDR,
        }),
        Cis2Event::Transfer(TransferEvent {
            token_id: TOKEN_0,
            amount:   TokenAmountU64(25), // Transfer made to Charlie.
            from:     BOB_ADDR,
            to:       CHARLIE_ADDR,
        }),
    ]);
}

/// Helper function that sets up the contract with two types of tokens minted to
/// Alice. She has 400 of `TOKEN_0` and 1 of `TOKEN_1`.
fn initialize_contract_with_alice_tokens(
    royalty_percentage: u8,
) -> (Chain, ContractAddress, ContractInvokeSuccess) {
    let (mut chain, contract_address) = initialize_chain_and_contract();

    let mint_params = MintParams {
        owner: ALICE_ADDR,
        tokens: BTreeMap::from_iter(vec![(TOKEN_0, 400.into()), (TOKEN_1, 1.into())]),
        royalty_percentage,
    };

    // Mint two tokens to Alice.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi_royalties.mint".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&mint_params).expect("Mint params"),
        })
        .expect("Mint tokens");

    (chain, contract_address, update)
}

/// Setup chain and contract.
///
/// Also creates the three accounts, Alice, Bob, and Charlie and initializes the
/// contract.
///
/// Alice is the owner of the contract.
fn initialize_chain_and_contract() -> (Chain, ContractAddress) {
    let mut chain = Chain::new();

    // Create some accounts on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(CHARLIE, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

    let parameter = InitParams {
        pay_royalty: true,
    };

    // Initialize the auction contract.
    let init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_cis2_multi_royalties".to_string()),
            param:     OwnedParameter::from_serial(&parameter).expect("Init params"),
        })
        .expect("Initialize contract");

    (chain, init.contract_address)
}
