//! Tests for the sponsored-tx-enabled-auction smart contract.
use concordium_smart_contract_testing::*;
use concordium_std::MetadataUrl;
use track_and_trace::*;

/// The test accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(AccountAddress([0; 32]));

const SIGNER: Signer = Signer::with_one_key();
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

#[test]
fn test_add_item() {
    let (mut chain, track_and_trace_contract_address) = initialize_chain_and_contract();

    // Create the InitParameter.
    let parameter = Some(MetadataUrl {
        url:  "https://some.example/".to_string(),
        hash: None,
    });

    // Add item.
    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::from_ccd(0),
            address:      track_and_trace_contract_address,
            receive_name: OwnedReceiveName::new_unchecked("track_and_trace.createItem".to_string()),
            message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
        })
        .expect("Should be able to add Item");

    // Check operator in state
    let test = view(&chain, track_and_trace_contract_address);

    print!("{:?}", test);

    let parameter = ChangeItemStatusParams {
        /// The address that has been its role revoked.
        item_id:         0u64,
        new_status:      Status::InStore,
        additional_data: AdditionalData {
            bytes: vec![],
        },
    };

    // Add item.
    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::from_ccd(0),
            address:      track_and_trace_contract_address,
            receive_name: OwnedReceiveName::new_unchecked(
                "track_and_trace.changeItemStatus".to_string(),
            ),
            message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
        })
        .expect("Should be able to add Item");

    // Check operator in state
    let test = view(&chain, track_and_trace_contract_address);

    print!("{:?}", test);
}

// Get the `TokenIdU8(1)` balances for Alice and the auction contract.
fn view(chain: &Chain, track_and_trace_contract_address: ContractAddress) -> ViewState {
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("track_and_trace.view".to_string()),
            address:      track_and_trace_contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke view");

    invoke.parse_return_value().expect("BalanceOf return value")
}

/// Setup auction and chain.
fn initialize_chain_and_contract() -> (Chain, ContractAddress) {
    let mut chain = Chain::builder().build().expect("Should be able to build chain");

    // Create some accounts on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));

    // Load and deploy the track_and_trace module.
    let module = module_load_v1("./concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

    // Initialize the track_and_trace contract.
    let track_and_trace = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_track_and_trace".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize track_and_trace contract");

    (chain, track_and_trace.contract_address)
}
