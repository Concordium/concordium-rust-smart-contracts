//! Tests for the factory smart contract.
use concordium_smart_contract_testing::*;
use concordium_std::{Cursor, Deserial, Reject};
use factory_smart_contract::{
    factory::FactoryError,
    product::{Product, ProductState},
};

/// The test accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const BOB: AccountAddress = AccountAddress([1; 32]);

const SIGNER: Signer = Signer::with_one_key();
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

/// Test the case of producing two products from one factory.
#[test]
fn test_success() {
    let (mut chain, module_ref) = initialize_chain();
    // Set up the factory instance.
    let factory = create_factory(&mut chain, module_ref);

    // Create a product instance.
    let product = create_product(&mut chain, module_ref, ALICE);
    // Check that it is uninitialized
    let prod_state = view_product(&chain, product).expect("Get view of uninitialized product");
    assert_eq!(prod_state, ProductState::Uninitialized);
    // "Produce" the product with the factory.
    call_produce(&mut chain, factory, product, ALICE).expect("Produce successful");
    // Check that it is initialized as we expect.
    let prod_state = view_product(&chain, product).expect("Get view of initialized product");
    assert_eq!(
        prod_state,
        ProductState::Initialized(Product { factory, index: 0 })
    );

    // Create and produce a second product (from a different account), and check the
    // result.
    let product2 = create_product(&mut chain, module_ref, BOB);
    call_produce(&mut chain, factory, product2, BOB).expect("Produce successful");
    let prod_state = view_product(&chain, product2).expect("Get view of initialized product");
    assert_eq!(
        prod_state,
        ProductState::Initialized(Product { factory, index: 1 })
    );

    // Check that the factory records having 2 products, and that they match what we
    // expect.
    assert_eq!(
        view_product_count(&chain, factory).expect("View product count successful"),
        2
    );
    assert_eq!(
        view_product_at(&chain, factory, 0).expect("View of product at index"),
        product
    );
    assert_eq!(
        view_product_at(&chain, factory, 1).expect("View of product at index"),
        product2
    );
}

/// Test that a product instance cannot be produced using an account that did
/// not create the product instance.
#[test]
fn test_not_authorized() {
    let (mut chain, module_ref) = initialize_chain();
    let factory = create_factory(&mut chain, module_ref);
    // ALICE creates the product instance, but BOB invokes produce on the factory.
    // This should fail.
    let product = create_product(&mut chain, module_ref, ALICE);
    let err = call_produce(&mut chain, factory, product, BOB).expect_err(
        "Should fail when product is called from a different account than the creator of the \
         product.",
    );
    assert_eq!(
        err.reject_code(),
        Some(
            Reject::from(FactoryError::InitializeFailed)
                .error_code
                .get()
        ),
        "Reject code should be InitializeFailed"
    );
}

/// Test that a product cannot be produced twice (by the same factory).
#[test]
fn test_double_produce() {
    let (mut chain, module_ref) = initialize_chain();
    let factory = create_factory(&mut chain, module_ref);
    let product = create_product(&mut chain, module_ref, ALICE);
    call_produce(&mut chain, factory, product, ALICE).expect("Produce successful");
    let err = call_produce(&mut chain, factory, product, ALICE)
        .expect_err("Should fail when product has already been initialized.");
    assert_eq!(
        err.reject_code(),
        Some(
            Reject::from(FactoryError::InitializeFailed)
                .error_code
                .get()
        ),
        "Reject code should be InitializeFailed"
    );
}

/// Test that a product cannot be produced twice (by different factories).
#[test]
fn test_double_produce_second_factory() {
    let (mut chain, module_ref) = initialize_chain();
    let factory = create_factory(&mut chain, module_ref);
    let product = create_product(&mut chain, module_ref, ALICE);
    call_produce(&mut chain, factory, product, ALICE).expect("Produce successful");
    let factory2 = create_factory(&mut chain, module_ref);
    let err = call_produce(&mut chain, factory2, product, ALICE)
        .expect_err("Should fail when product has already been initialized.");
    assert_eq!(
        err.reject_code(),
        Some(
            Reject::from(FactoryError::InitializeFailed)
                .error_code
                .get()
        ),
        "Reject code should be InitializeFailed"
    );
}

/// Test that `produce` fails when called with an instance of a contract other
/// than the product, namely an instance of the factory contract.
/// Note, this only tests the functionality that distinguishes on the contract
/// name, not on the contract module reference.
#[test]
fn test_wrong_product() {
    let (mut chain, module_ref) = initialize_chain();
    let factory = create_factory(&mut chain, module_ref);
    let factory2 = create_factory(&mut chain, module_ref);
    let err = call_produce(&mut chain, factory, factory2, ALICE)
        .expect_err("Should fail with incorrect product contract");
    assert_eq!(
        err.reject_code(),
        Some(Reject::from(FactoryError::InvalidProduct).error_code.get()),
        "Reject code should be InvalidProduct"
    );
}

/// Helper function to set up the chain with initial accounts, the module
/// deployed.
fn initialize_chain() -> (Chain, ModuleReference) {
    let mut chain = Chain::new();

    // Create some accounts on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));

    // Load and deploy the module.
    let module = module_load_v1("concordium-out/module.wasm.v1").expect("Module exists");
    let deployment = chain
        .module_deploy_v1(SIGNER, ALICE, module)
        .expect("Deploy valid module");

    (chain, deployment.module_reference)
}

/// Helper to create an instance of the factory smart contract.
fn create_factory(chain: &mut Chain, module_ref: ModuleReference) -> ContractAddress {
    chain
        .contract_init(
            SIGNER,
            ALICE,
            Energy::from(10000),
            InitContractPayload {
                amount: Amount::zero(),
                mod_ref: module_ref,
                init_name: OwnedContractName::new_unchecked("init_factory".to_string()),
                param: OwnedParameter::empty(),
            },
        )
        .expect("Initialize factory")
        .contract_address
}

/// Helper to create an instance of the product smart contract.
fn create_product(
    chain: &mut Chain,
    module_ref: ModuleReference,
    creator: AccountAddress,
) -> ContractAddress {
    chain
        .contract_init(
            SIGNER,
            creator,
            Energy::from(10000),
            InitContractPayload {
                amount: Amount::zero(),
                mod_ref: module_ref,
                init_name: OwnedContractName::new_unchecked("init_product".to_string()),
                param: OwnedParameter::empty(),
            },
        )
        .expect("Initialize product")
        .contract_address
}

/// Helper to call `produce` on the factory smart contract.
fn call_produce(
    chain: &mut Chain,
    factory: ContractAddress,
    product: ContractAddress,
    invoker: AccountAddress,
) -> Result<ContractInvokeSuccess, ContractInvokeError> {
    chain.contract_update(
        SIGNER,
        invoker,
        Address::Account(invoker),
        Energy::from(100000),
        UpdateContractPayload {
            amount: Amount::zero(),
            address: factory,
            receive_name: OwnedReceiveName::new_unchecked("factory.produce".to_string()),
            message: OwnedParameter::from_serial(&product).unwrap(),
        },
    )
}

/// Helper to view the state of a product contract.
fn view_product(
    chain: &Chain,
    product: ContractAddress,
) -> Result<ProductState, ContractInvokeError> {
    let success = chain.contract_invoke(
        ALICE,
        Address::Account(ALICE),
        Energy::from(100000),
        UpdateContractPayload {
            amount: Amount::zero(),
            address: product,
            receive_name: OwnedReceiveName::new_unchecked("product.view".to_string()),
            message: OwnedParameter::empty(),
        },
    )?;
    Ok(
        ProductState::deserial(&mut Cursor::new(success.return_value))
            .expect("View result deserialization failure"),
    )
}

/// Helper to view the total number of products that have been produced by a
/// factory.
fn view_product_count(chain: &Chain, factory: ContractAddress) -> Result<u64, ContractInvokeError> {
    let success = chain.contract_invoke(
        ALICE,
        Address::Account(ALICE),
        Energy::from(100000),
        UpdateContractPayload {
            amount: Amount::zero(),
            address: factory,
            receive_name: OwnedReceiveName::new_unchecked("factory.view_product_count".to_string()),
            message: OwnedParameter::empty(),
        },
    )?;
    Ok(u64::deserial(&mut Cursor::new(success.return_value))
        .expect("View result deserialization failure"))
}

/// Helper to view the address of a product assigned a particular index by a
/// factory.
fn view_product_at(
    chain: &Chain,
    factory: ContractAddress,
    index: u64,
) -> Result<ContractAddress, ContractInvokeError> {
    let success = chain.contract_invoke(
        ALICE,
        Address::Account(ALICE),
        Energy::from(100000),
        UpdateContractPayload {
            amount: Amount::zero(),
            address: factory,
            receive_name: OwnedReceiveName::new_unchecked("factory.view_product".to_string()),
            message: OwnedParameter::from_serial(&index).unwrap(),
        },
    )?;
    Ok(
        ContractAddress::deserial(&mut Cursor::new(success.return_value))
            .expect("View result deserialization failure"),
    )
}
