use cis2_dynamic_nft::{
    ContractError, ContractTokenAmount, ContractTokenId, ContractTokenMetadataQueryParams,
    MintParam, MintParams, ViewAddressState, ViewState,
};
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::*;
/// The tests accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = AccountAddress([1; 32]);
const BOB_ADDR: Address = Address::Account(BOB);

/// Token IDs.
const TOKEN_0: ContractTokenId = TokenIdU8(3);
const TOKEN_2: ContractTokenId = TokenIdU8(5);

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

/// A signer with one key.
const SIGNER: Signer = Signer::with_one_key();

/// Test that a transfer fails when the sender is neither an operator or the
/// owner. In particular, Bob will attempt to transfer some of Alice's tokens to
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
        amount:   TokenAmountU64(1),
        data:     AdditionalData::empty(),
    }]);

    // Notice that Bob is the sender/invoker.
    let update = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_dynamic_nft.transfer".to_string()),
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
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_dynamic_nft.updateOperator".to_string(),
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
            receive_name: OwnedReceiveName::new_unchecked("cis2_dynamic_nft.transfer".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&transfer_params).expect("Transfer params"),
        })
        .expect("Transfer tokens");

    // Check that Bob now has 1 of `TOKEN_0` and Alice has 399. Also check that
    // Alice still has 400 `TOKEN_2`.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_dynamic_nft.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.state, vec![
        (ALICE_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 399.into()), (TOKEN_2, 400.into())],
            operators: vec![BOB_ADDR],
        }),
        (BOB_ADDR, ViewAddressState {
            balances:  vec![(TOKEN_0, 1.into())],
            operators: Vec::new(),
        }),
    ]);
}

/// Test minting succeeds and the tokens are owned by the given address and
/// the appropriate events are logged. When token is minted first index of
/// the Metadata URL vector will be logged, if there is only one MetadatUrl then
/// it will be logged.
#[test]
fn test_minting() {
    let (chain, contract_address, update) = initialize_contract_with_alice_tokens();

    // Invoke the view entrypoint and check that the tokens are owned by Alice.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_dynamic_nft.view".to_string()),
            address:      contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");

    // Check that the tokens are owned by Alice.
    let rv: ViewState = invoke.parse_return_value().expect("ViewState return value");
    assert_eq!(rv.tokens[..], [TOKEN_0, TOKEN_2]);
    assert_eq!(rv.state, vec![(ALICE_ADDR, ViewAddressState {
        balances:  vec![(TOKEN_0, 400.into()), (TOKEN_2, 400.into())],
        operators: Vec::new(),
    })]);

    // Check that the events are logged.
    let events = update.events().flat_map(|(_addr, events)| events);

    let events: Vec<Cis2Event<ContractTokenId, ContractTokenAmount>> =
        events.map(|e| e.parse().expect("Deserialize event")).collect();

    assert_eq!(events, [
        Cis2Event::Mint(MintEvent {
            token_id: TokenIdU8(5),
            amount:   TokenAmountU64(400),
            owner:    ALICE_ADDR,
        }),
        Cis2Event::TokenMetadata(TokenMetadataEvent {
            token_id:     TokenIdU8(5),
            metadata_url: MetadataUrl {
                url:  format!("https://some.example/token/3/{TOKEN_2}").to_string(),
                hash: None,
            },
        }),
    ]);
}

/// Test upgrading the Metadata token as the contract owner. Once a token is
/// upgraded, the TokenMetadata event will be emitted and it should contain
/// the next MetadataUrl in the Metadata URLs vector and similarly
/// `tokenMetadata` function should return the last MetadataUrl.

#[test]
fn test_upgrade() {
    let (mut chain, contract_address, _update) = initialize_contract_with_alice_tokens();
    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_dynamic_nft.upgrade".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&TOKEN_0).expect("TokenId"),
        })
        .expect("Upgrade tokens");
    // Check that the events are logged.
    let events = _update.events().flat_map(|(_addr, events)| events);

    let events: Vec<Cis2Event<ContractTokenId, ContractTokenAmount>> =
        events.map(|e| e.parse().expect("Deserialize event")).collect();

    assert_eq!(events, [Cis2Event::TokenMetadata(TokenMetadataEvent {
        token_id:     TokenIdU8(3),
        metadata_url: MetadataUrl {
            url:  format!("https://some.example/token/2/{TOKEN_0}").to_string(),
            hash: None,
        },
    }),]);
    let mut token_param = ContractTokenMetadataQueryParams {
        queries: vec![TOKEN_0],
    };
    token_param.queries.insert(0, TOKEN_0);
    // Invoke the tokenMetadata entrypoint and check what MetadataUrl returns
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "cis2_dynamic_nft.tokenMetadata".to_string(),
            ),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&token_param).expect("tokenMetada params"),
        })
        .expect("Invoke tokenMetadata");

    let rv: TokenMetadataQueryResponse =
        invoke.parse_return_value().expect("tokenMetadata return value");
    let expected_metadata = MetadataUrl {
        url:  format!("https://some.example/token/2/{TOKEN_0}"),
        hash: None,
    };
    assert_eq!(rv.0.get(0), Some(&expected_metadata));
}

/// Helper function that sets up the contract with two types of tokens minted to
/// Alice. She has 400 of `TOKEN_0` and 400 of `TOKEN_2`.
fn initialize_contract_with_alice_tokens(
) -> (concordium_smart_contract_testing::Chain, ContractAddress, ContractInvokeSuccess) {
    let (mut chain, contract_address) = initialize_chain_and_contract();

    let mut test_v1 = Vec::new();
    test_v1.push(MetadataUrl {
        url:  format!("https://some.example/token/1/{TOKEN_0}"),
        hash: None,
    });
    // we will need the following to test the upgrade function.
    test_v1.push(MetadataUrl {
        url:  format!("https://some.example/token/2/{TOKEN_0}"),
        hash: None,
    });

    let mut test_v2 = Vec::new();
    test_v2.push(MetadataUrl {
        url:  format!("https://some.example/token/3/{TOKEN_2}"),
        hash: None,
    });
    let mint_param_1 = MintParam {
        token_amount: 400.into(),
        metadata_url: test_v1,
    };
    let mut tok = collections::BTreeMap::new();

    tok.insert(TOKEN_0, mint_param_1);
    let mint_params = MintParams {
        owner:  ALICE_ADDR,
        tokens: tok,
    };

    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_dynamic_nft.mint".to_string()),
            address:      contract_address,
            message:      OwnedParameter::from_serial(&mint_params).expect("Mint params"),
        })
        .expect("Mint tokens");

    let mint_param_2 = MintParam {
        token_amount: 400.into(),
        metadata_url: test_v2,
    };
    let mut tok2 = collections::BTreeMap::new();

    tok2.insert(TOKEN_2, mint_param_2);
    let mint_params = MintParams {
        owner:  ALICE_ADDR,
        tokens: tok2,
    };

    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_dynamic_nft.mint".to_string()),
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
fn initialize_chain_and_contract() -> (concordium_smart_contract_testing::Chain, ContractAddress) {
    let mut chain = concordium_smart_contract_testing::Chain::new();

    // Create some accounts accounts on the chain.
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
            init_name: OwnedContractName::new_unchecked("init_cis2_dynamic_nft".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize contract");

    (chain, init.contract_address)
}
