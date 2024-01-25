//! Tests for the sponsored-tx-enabled-auction smart contract.
use concordium_smart_contract_testing::*;
use concordium_std::MetadataUrl;
use track_and_trace::*;

/// The test accounts.
const ADMIN: AccountAddress = AccountAddress([0; 32]);
const ADMIN_ADDR: Address = Address::Account(AccountAddress([0; 32]));
const PRODUCER: AccountAddress = AccountAddress([1; 32]);
const PRODUCER_ADDR: Address = Address::Account(AccountAddress([1; 32]));
const TRANSPORTER: AccountAddress = AccountAddress([2; 32]);
const TRANSPORTER_ADDR: Address = Address::Account(AccountAddress([2; 32]));
const SELLER: AccountAddress = AccountAddress([3; 32]);
const SELLER_ADDR: Address = Address::Account(AccountAddress([3; 32]));

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
        .contract_update(SIGNER, ADMIN, ADMIN_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::from_ccd(0),
            address:      track_and_trace_contract_address,
            receive_name: OwnedReceiveName::new_unchecked("track_and_trace.createItem".to_string()),
            message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
        })
        .expect("Should be able to add Item");

    // Check operator in state
    let test = view(&chain, track_and_trace_contract_address);

    println!("{:?}", test);

    let parameter = ChangeItemStatusParams {
        /// The address that has been its role revoked.
        item_id:         0u64,
        additional_data: AdditionalData {
            bytes: vec![],
        },
    };

    // Add item.
    let _update = chain
        .contract_update(
            SIGNER,
            PRODUCER,
            PRODUCER_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::from_ccd(0),
                address:      track_and_trace_contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "track_and_trace.changeItemStatus".to_string(),
                ),
                message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
            },
        )
        .expect("Should be able to add Item");

    // Check operator in state
    let test = view(&chain, track_and_trace_contract_address);

    println!("{:?}", test);

    let parameter = ChangeItemStatusParamsByAdmin {
        /// The address that has been its role revoked.
        item_id:         0u64,
        new_status:      Status::Sold,
        additional_data: AdditionalData {
            bytes: vec![],
        },
    };

    // Add item.
    let _update = chain
        .contract_update(SIGNER, ADMIN, ADMIN_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::from_ccd(0),
            address:      track_and_trace_contract_address,
            receive_name: OwnedReceiveName::new_unchecked(
                "track_and_trace.changeItemStatusByAdmin".to_string(),
            ),
            message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
        })
        .expect("Should be able to add Item");

    // Check operator in state
    let test = view(&chain, track_and_trace_contract_address);
    println!("{:?}", test);
}

// Get the `TokenIdU8(1)` balances for ADMIN and the auction contract.
fn view(chain: &Chain, track_and_trace_contract_address: ContractAddress) -> ViewState {
    let invoke = chain
        .contract_invoke(ADMIN, ADMIN_ADDR, Energy::from(10000), UpdateContractPayload {
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
    chain.create_account(Account::new(ADMIN, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(PRODUCER, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(TRANSPORTER, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(SELLER, ACC_INITIAL_BALANCE));

    // Load and deploy the track_and_trace module.
    let module = module_load_v1("./concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ADMIN, module).expect("Deploy valid module");

    // Initialize the track_and_trace contract.
    let track_and_trace = chain
        .contract_init(SIGNER, ADMIN, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_track_and_trace".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize track_and_trace contract");

    // Grant PRODUCER role
    let grant_role_params = GrantRoleParams {
        address: PRODUCER_ADDR,
        role:    Roles::PRODUCER,
    };

    let _update = chain
        .contract_update(SIGNER, ADMIN, ADMIN_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("track_and_trace.grantRole".to_string()),
            address:      track_and_trace.contract_address,
            message:      OwnedParameter::from_serial(&grant_role_params)
                .expect("GrantRole params"),
        })
        .expect("PRODUCER should be granted role");

    // Grant TRANSPORTER role
    let grant_role_params = GrantRoleParams {
        address: TRANSPORTER_ADDR,
        role:    Roles::TRANSPORTER,
    };

    let _update = chain
        .contract_update(SIGNER, ADMIN, ADMIN_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("track_and_trace.grantRole".to_string()),
            address:      track_and_trace.contract_address,
            message:      OwnedParameter::from_serial(&grant_role_params)
                .expect("GrantRole params"),
        })
        .expect("TRANSPORTER should be granted role");

    // Grant SELLER role
    let grant_role_params = GrantRoleParams {
        address: SELLER_ADDR,
        role:    Roles::SELLER,
    };

    let _update = chain
        .contract_update(SIGNER, ADMIN, ADMIN_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("track_and_trace.grantRole".to_string()),
            address:      track_and_trace.contract_address,
            message:      OwnedParameter::from_serial(&grant_role_params)
                .expect("GrantRole params"),
        })
        .expect("SELLER should be granted role");
    (chain, track_and_trace.contract_address)
}
