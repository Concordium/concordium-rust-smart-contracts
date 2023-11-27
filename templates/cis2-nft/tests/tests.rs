//! Tests for the `{{crate_name}}` contract.
use {{crate_name}}::*;
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::collections::BTreeSet;

/// The tests accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = AccountAddress([1; 32]);
const BOB_ADDR: Address = Address::Account(BOB);

/// Token IDs.
const TOKEN_0: ContractTokenId = TokenIdU32(2);
const TOKEN_1: ContractTokenId = TokenIdU32(42);

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

/// A signer for all the transactions.
const SIGNER: Signer = Signer::with_one_key();

/// Test minting succeeds and the tokens are owned by the given address and
/// the appropriate events are logged.
#[test]
fn test_minting() {
    let (chain, contract_address, update) = initialize_contract_with_alice_tokens();

    // Invoke the view entrypoint and check that the tokens are owned by Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");

    // Check that the tokens are owned by Alice.
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.all_tokens[..], [TOKEN_0, TOKEN_1]);
    assert_eq!(rv.state, vec![(ALICE_ADDR, ViewAddressState {
        owned_tokens: vec![TOKEN_0, TOKEN_1],
        operators:    Vec::new(),
    })]);

    // Check that the events are logged.
    let events = update.events().flat_map(|(_addr, events)| events);

    let events: Vec<Cis2Event<ContractTokenId, ContractTokenAmount>> =
        events.map(|e| e.parse().expect("Deserialize event")).collect();

    assert_eq!(events, [
        Cis2Event::Mint(MintEvent {
            token_id: TokenIdU32(2),
            amount:   TokenAmountU8(1),
            owner:    ALICE_ADDR,
        }),
        Cis2Event::TokenMetadata(TokenMetadataEvent {
            token_id:     TokenIdU32(2),
            metadata_url: MetadataUrl {
                url:  format!("{TOKEN_METADATA_BASE_URL}02000000"),
                hash: None,
            },
        }),
        Cis2Event::Mint(MintEvent {
            token_id: TokenIdU32(42),
            amount:   TokenAmountU8(1),
            owner:    ALICE_ADDR,
        }),
        Cis2Event::TokenMetadata(TokenMetadataEvent {
            token_id:     TokenIdU32(42),
            metadata_url: MetadataUrl {
                url:  format!("{TOKEN_METADATA_BASE_URL}2A000000"),
                hash: None,
            },
        }),
    ]);
}

/// Test regular transfer where sender is the owner.
#[test]
fn test_account_transfer() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Transfer `TOKEN_0` from Alice to Bob.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU8(1),
        data:     AdditionalData::empty(),
    }]);

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.transfer".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Bob now has `TOKEN_0` and that Alice still has `TOKEN_1`.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.state, vec![
        (ALICE_ADDR, ViewAddressState {
            owned_tokens: vec![TOKEN_1],
            operators:    Vec::new(),
        }),
        (BOB_ADDR, ViewAddressState {
            owned_tokens: vec![TOKEN_0],
            operators:    Vec::new(),
        }),
    ]);

    // Check that the events are logged.
    let events = update
        .events()
        .flat_map(|(_addr, events)| events.iter().map(|e| e.parse().expect("Deserialize event")))
        .collect::<Vec<Cis2Event<_, _>>>();

    assert_eq!(events, [Cis2Event::Transfer(TransferEvent {
        token_id: TOKEN_0,
        amount:   TokenAmountU8(1),
        from:     ALICE_ADDR,
        to:       BOB_ADDR,
    }),]);
}

/// Test that you can add an operator.
/// Initialize the contract with two tokens owned by Alice.
/// Then add Bob as an operator for Alice.
#[test]
fn test_add_operator() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Add Bob as an operator for Alice.
    let params = UpdateOperatorParams(vec![UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    }]);

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.updateOperator".to_string()),
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
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.operatorOf".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&query_params).expect("OperatorOf params"),
        })
        .expect("Invoke view");

    let rv: OperatorOfQueryResponse = invoke.parse_return_value().expect("OperatorOf return value");
    assert_eq!(rv, OperatorOfQueryResponse(vec![true]));
}

/// Test that a transfer fails when the sender is neither an operator or the
/// owner. In particular, Bob will attempt to transfer one of Alice's tokens to
/// himself.
#[test]
fn test_unauthorized_sender() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Construct a transfer of `TOKEN_0` from Alice to Bob, which will be submitted
    // by Bob.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU8(1),
        data:     AdditionalData::empty(),
    }]);

    // Notice that Bob is the sender/invoker.
    let update = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.transfer".to_string()),
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
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens();

    // Add Bob as an operator for Alice.
    let params = UpdateOperatorParams(vec![UpdateOperator {
        update:   OperatorUpdate::Add,
        operator: BOB_ADDR,
    }]);
    chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.updateOperator".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&params).expect("UpdateOperator params"),
        })
        .expect("Update operator");

    // Let Bob make a transfer to himself on behalf of Alice.
    let transfer_params = TransferParams::from(vec![concordium_cis2::Transfer {
        from:     ALICE_ADDR,
        to:       Receiver::Account(BOB),
        token_id: TOKEN_0,
        amount:   TokenAmountU8(1),
        data:     AdditionalData::empty(),
    }]);

    chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.transfer".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Bob now has `TOKEN_0` and that Alice still has `TOKEN_1`.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.state, vec![
        (ALICE_ADDR, ViewAddressState {
            owned_tokens: vec![TOKEN_1],
            operators:    vec![BOB_ADDR],
        }),
        (BOB_ADDR, ViewAddressState {
            owned_tokens: vec![TOKEN_0],
            operators:    Vec::new(),
        }),
    ]);
}

/// Helper function that sets up the contract with two tokens minted to
/// Alice, `TOKEN_0` and `TOKEN_1`.
fn initialize_contract_with_alice_tokens() -> (Chain, ContractAddress, ContractInvokeSuccess) {
    let (mut chain, contract_address) = initialize_chain_and_contract();

    let mint_params = MintParams {
        owner:  ALICE_ADDR,
        tokens: BTreeSet::from_iter(vec![TOKEN_0, TOKEN_1]),
    };

    // Mint two tokens to Alice.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("{{crate_name}}.mint".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&mint_params).expect("Mint params"),
        })
        .expect("Mint tokens");

    (chain, contract_address, update)
}

/// Setup chain and contract.
///
/// Also creates the two accounts, Alice and Bob.
///
/// Alice is the owner of the contract.
fn initialize_chain_and_contract() -> (Chain, ContractAddress) {
    let mut chain = Chain::new();

    // Create some accounts on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

    // Initialize the auction contract.
    let init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_{{crate_name}}".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize contract");

    (chain, init.contract_address)
}
