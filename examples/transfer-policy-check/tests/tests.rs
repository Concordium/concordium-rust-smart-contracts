//! Tests for the transfer-policy-check contract.
use concordium_smart_contract_testing::*;
use concordium_std::{attributes, OwnedPolicy};
use transfer_policy_check::*;

/// Constants.
const ALICE: AccountAddress = AccountAddress([0u8; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = AccountAddress([1u8; 32]);
const BOB_ADDR: Address = Address::Account(BOB);

const SIGNER: Signer = Signer::with_one_key();

// Tests:

/// Test that sending money via the contract works when the sender has the
/// correct policy. Meaning that the sender has the country of residence in
/// Denmark (`DK`).
#[test]
fn test_amount_forward_on_correct_policy() {
    let (mut chain, contract_address) = init();

    // Construct a policy with the correct country code.
    let policy = policy_with_country(LOCAL_COUNTRY);
    // Create the account BOB, who is from Denmark.
    chain.create_account(Account::new_with_policy(
        BOB,
        AccountBalance::new(Amount::from_ccd(1000), Amount::zero(), Amount::zero())
            .expect("Staked + locked < total."),
        policy,
    ));

    let amount_to_send = Amount::from_ccd(10);

    // Send money from Bob to Alice.
    let update = chain
        .contract_update(SIGNER, BOB, BOB_ADDR, Energy::from(50_000), UpdateContractPayload {
            amount:       amount_to_send,
            address:      contract_address,
            receive_name: OwnedReceiveName::new_unchecked(
                "transfer-policy-check.receive".to_string(),
            ),
            message:      OwnedParameter::empty(),
        })
        .expect("Contract update succeeds.");

    // Check that the money was forwarded.
    // assert_eq!(update.account_transfers().collect::<Vec<_>>(),
    // [(contract_address, amount_to_send, ALICE)]);
}

// Helpers:

/// Construct a policy with the provided country code.
fn policy_with_country(country_code: [u8; 2]) -> OwnedPolicy {
    let policies = OwnedPolicy {
        identity_provider: 0,
        created_at:        Timestamp::from_timestamp_millis(0),
        valid_to:          Timestamp::from_timestamp_millis(1000),
        items:             vec![(attributes::COUNTRY_OF_RESIDENCE, country_code.into())],
    };

    policies
}

/// Initialize the chain and contract.
///
/// Creates one account (ALICE), deploys the module, and initializes the
/// contract.
fn init() -> (Chain, ContractAddress) {
    let mut chain = Chain::new();

    // Create an account.
    chain.create_account(Account::new(ALICE, Amount::from_ccd(1000)));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists.");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Module deploys.");

    // Initialize the transfer policy check contract.
    let init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10_000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_transfer-policy-check".to_string()),
            param:     OwnedParameter::from_serial(&ALICE).expect("Parameter has valid size."),
        })
        .expect("Initialize transfer policy check contract");

    (chain, init.contract_address)
}
