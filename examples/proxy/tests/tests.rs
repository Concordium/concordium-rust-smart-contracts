//! Tests for the proxy example.
use concordium_smart_contract_testing::*;

const ALICE: AccountAddress = AccountAddress([0u8; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const SIGNER: Signer = Signer::with_one_key();

/// Tests that the proxy forwards the invocation to the proxied contract and
/// that it returns the return value with any additional bytes prepended (see
/// `RawReturnValue`s `Serial` implemenetation for details).
#[test]
fn test_forwards_and_returns_data_unaltered() {
    let mut chain = Chain::new();

    // Create an account.
    chain.create_account(Account::new(ALICE, Amount::from_ccd(1000)));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists.");
    let deployment = chain.module_deploy_v1(SIGNER, ALICE, module).expect("Module deploys.");

    // Initialize the world_appender contract.
    let init_world_appender = chain
        .contract_init(SIGNER, ALICE, Energy::from(10_000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_world_appender".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize world_appender contract");

    // Create the proxy contract.
    let init_proxy = chain
        .contract_init(SIGNER, ALICE, Energy::from(10_000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_proxy".to_string()),
            param:     OwnedParameter::from_serial(&init_world_appender.contract_address)
                .expect("Serialize appender contract address parameter"),
        })
        .expect("Initialize proxy contract");

    // Construct the parameter.
    let parameter = "hello";

    // Call the `append` entrypoint via the proxy contract. Send `"hello"` as the
    // input parameter.
    let update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10_000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      init_proxy.contract_address, // Note that this is the proxy address.
            receive_name: OwnedReceiveName::new_unchecked("proxy.append".to_string()),
            message:      OwnedParameter::from_serial(&parameter).expect("Serialize parameter"),
        })
        .expect("Invoke proxy contract");

    // Check that the return value can be deserialized and is correct.
    // This ensures that the `RawReturnValue`s serial implementation is correct,
    // in that it *doesn't* include the option tag and length values in the return
    // value. If they were included, the string would have some extra bytes at
    // the beginning.
    let return_value: String = from_bytes(&update.return_value).expect("Deserialize return value");
    assert_eq!(return_value, "hello, world");
}
