//! Tests for the smart contract oracle integration.
use concordium_smart_contract_testing::*;
use concordium_std::{PublicKeyEd25519, SignatureEd25519};
mod types;
use smart_contract_oracle_integration::PriceData;
use types::*;

/// The tests accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);

const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);
const SIGNER: Signer = Signer::with_one_key();

const DUMMY_SIGNATURE: SignatureEd25519 = SignatureEd25519([
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
]);

/// Test updating the price.
#[test]
fn test_updating_price() {
    let (mut chain, umbrella_feeds_contract_address, integration_contract_address) =
        initialize_chain_and_contract();

    let feed_name: String = String::from("CCD-USD");

    let price_data = PriceData {
        data:      7,
        heartbeat: 12,
        timestamp: Timestamp::from_timestamp_millis(9),
        price:     4,
    };

    use ed25519_dalek::{Signer, SigningKey};

    // The private key has to associated with the public key that is registered in
    // the `staking_bank` contract.
    let signing_key = SigningKey::from_bytes(&[
        106, 51, 214, 254, 87, 138, 112, 190, 28, 26, 194, 158, 91, 136, 124, 146, 252, 160, 196,
        76, 167, 213, 200, 32, 166, 87, 63, 193, 18, 95, 172, 49,
    ]);

    let verifying_key = signing_key.verifying_key();

    // The `viewMessageHash` function uses the input parameter `UpdateParams`.
    // The `UpdateParams` type includes a `signers_and_signatures` field.
    // Because this field (`signers_and_signatures`) is not
    // read in the `viewMessageHash` function, any value can be used and we choose
    // to use `DUMMY_SIGNATURE` and `verifying_key` in the test case below.
    let mut param = UpdateParams {
        signers_and_signatures: vec![(PublicKeyEd25519(verifying_key.to_bytes()), DUMMY_SIGNATURE)],
        message:                Message {
            contract_address: umbrella_feeds_contract_address,
            timestamp:        Timestamp::from_timestamp_millis(1000000000000),
            price_feed:       vec![(feed_name, price_data)],
        },
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      umbrella_feeds_contract_address,
            receive_name: OwnedReceiveName::new_unchecked(
                "umbrella_feeds.viewMessageHash".to_string(),
            ),
            message:      OwnedParameter::from_serial(&param)
                .expect("Should be a valid inut parameter"),
        })
        .expect("Should be able to query viewMessageHash");

    // Generate signature.
    let signature = signing_key.sign(&invoke.return_value);

    // Add signature to the input parameter.
    param.signers_and_signatures =
        vec![(PublicKeyEd25519(verifying_key.to_bytes()), SignatureEd25519(signature.to_bytes()))];

    // Updating price data in umbrella_feeds contract.
    let _update: ContractInvokeSuccess = chain
        .contract_update(
            SIGNER,
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      umbrella_feeds_contract_address,
                receive_name: OwnedReceiveName::new_unchecked("umbrella_feeds.update".to_string()),
                message:      OwnedParameter::from_serial(&param)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to update the price in the umbrella oracle protocol");

    // Updating the price data in the smart contract oracle integration.
    let _update = chain
        .contract_update(
            concordium_smart_contract_testing::Signer::with_one_key(),
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                amount:       Amount::zero(),
                address:      integration_contract_address,
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_oracle_integration.update_price".to_string(),
                ),
                message:      OwnedParameter::from_serial(&String::from("CCD-USD"))
                    .expect("Serialize parameter"),
            },
        )
        .expect("Should be able to update the price in the integration contract");

    // Invoke the `prices` entry point and check that the prices were updated.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_oracle_integration.prices".to_string(),
            ),
            address:      integration_contract_address,
            message:      OwnedParameter::empty(),
        })
        .expect("Invoke prices");

    let rv: Vec<(String, u128)> = invoke.parse_return_value().expect("View return value");

    assert_eq!(rv, vec![(String::from("CCD-USD"), 4)]);
}

/// Setup the umbrella oracle protocol and the smart_contract_oracle_integration
/// contract.
///
/// Create an account for ALICE.
fn initialize_chain_and_contract() -> (Chain, ContractAddress, ContractAddress) {
    let mut chain = Chain::builder().build().expect("Expect setting up the chain");

    // Create an account on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Deploy valid module");

    // Initialize the oracle integration contract.
    let init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked(
                "init_smart_contract_oracle_integration".to_string(),
            ),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize integration contract");

    // Load and deploy the Umbrella oracle protocol.

    // Deploying 'registry' contract
    let deployment_registry = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ALICE,
            module_load_v1("./umbrella-contract-modules/registry.wasm.v1")
                .expect("`registry.wasm.v1` module should be loaded"),
        )
        .expect("`registry.wasm.v1` deployment should always succeed");

    let initialization_registry = chain
        .contract_init(Signer::with_one_key(), ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment_registry.module_reference,
            init_name: OwnedContractName::new_unchecked("init_registry".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialization of `registry` should always succeed");

    // Deploying 'staking_bank' contract
    let deployment_staking_bank = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ALICE,
            module_load_v1("./umbrella-contract-modules/staking_bank.wasm.v1")
                .expect("`staking_bank.wasm.v1` module should be loaded"),
        )
        .expect("`staking_bank.wasm.v1` deployment should always succeed");

    let initialization_staking_bank = chain
        .contract_init(Signer::with_one_key(), ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment_staking_bank.module_reference,
            init_name: OwnedContractName::new_unchecked("init_staking_bank".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialization of `staking_bank` should always succeed");

    // Deploying 'umbrella_feeds' contract
    let deployment = chain
        .module_deploy_v1(
            Signer::with_one_key(),
            ALICE,
            module_load_v1("./umbrella-contract-modules/umbrella_feeds.wasm.v1")
                .expect("`Umbrella_feeds.wasm.v1` module should be loaded"),
        )
        .expect("`Umbrella_feeds.wasm.v1` deployment should always succeed");

    let input_parameter = InitParamsUmbrellaFeeds {
        registry:            initialization_registry.contract_address,
        required_signatures: 1,
        staking_bank:        initialization_staking_bank.contract_address,
        decimals:            4,
    };

    let initialization_umbrella_feeds = chain
        .contract_init(Signer::with_one_key(), ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_umbrella_feeds".to_string()),
            param:     OwnedParameter::from_serial(&input_parameter)
                .expect("`InitContractsParam` should be a valid inut parameter"),
        })
        .expect("Initialization of `umbrella_feeds` should always succeed");

    let input_parameter = ImportContractsParam {
        entries: vec![initialization_umbrella_feeds.contract_address],
    };

    // Importing the `umbrella_feeds` contract into the `registry` contract.
    let _update = chain
        .contract_update(
            Signer::with_one_key(),
            ALICE,
            Address::Account(ALICE),
            Energy::from(10000),
            UpdateContractPayload {
                address:      initialization_registry.contract_address,
                receive_name: OwnedReceiveName::new_unchecked("registry.importContracts".into()),
                message:      OwnedParameter::from_serial(&input_parameter)
                    .expect("`input_parameter` should be a valid inut parameter"),
                amount:       Amount::from_ccd(0),
            },
        )
        .expect("Should be able to importContracts");

    (chain, initialization_umbrella_feeds.contract_address, init.contract_address)
}
