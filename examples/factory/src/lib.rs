//! An example demonstrating how a factory pattern can be implemented with smart
//! contracts on Concordium.
//!
//! > **Important Note:** The factory pattern is not generally idiomatic on
//! > Concordium. In many cases, a more appropriate solution is to incorporate
//! > the factory and products into a single smart contract instance, rather
//! > than having a separate instance for each product. In other cases, a
//! > registry contract, which maintains an index of other contract instances,
//! > might be appropriate. However, a registry contract does not need to be
//! > responsible for instantiating the other contracts, as is the case in the
//! > factory pattern. (See the discussion below on "Alternatives to the factory
//! > pattern".)
//!
//! # Description
//!
//! This example shows how a factory pattern can be implemented with smart
//! contracts on Concordium. It consists of two smart contracts: the factory and
//! the product.
//!
//! In a typical factory pattern, the factory contract provides a `produce`
//! endpoint that constructs a new instance of the product contract. On
//! Concordium, however, it is not possible to create a new smart contract
//! instance within a receive method.
//!
//! To work around this, the new smart contract instance is first created in a
//! separate transaction. The address of this new smart contract is then passed
//! to the `produce` endpoint of the factory. As part of `produce`, the factory
//! calls an `initialize` method on the product.
//!
//! In the typical factory pattern, the factory controls which contract is
//! constructed and can be sure that the instance is newly constructed. In our
//! implementation, the factory does not directly construct the product. This
//! means that the factory **must check** that the supplied product is an
//! instance of the expected product contract. This is achieved by checking the
//! module reference and contract name match expected values. To ensure that the
//! product is indeed newly constructed, the factory calls an `initialize`
//! method on the product that will initialize its state, but fail if it has
//! already been initialized.
//!
//! In this example, both the factory and product are defined in the same
//! module, so the factory checks that the product's module reference is the
//! same as the factory's. If the contracts were defined in separate modules,
//! then the factory would need to know the module reference that products
//! should use. This could be hard-coded in the contract, or set as a parameter
//! when the factory is initialized.
//!
//! In this example the factory acts as a registry of all the products it has
//! "produced", assigning each a fresh index and recording the contract address
//! for each. The products are initialized with their index, and also keep a
//! record of the address of the factory contract that produced them. In a
//! practical application, the factory might supply additional paramaters when
//! initializing the products.
//!
//! # Security considerations
//!
//! Since the construction and initialization of the product occur in two
//! separate transactions, it is possible that a third party might try to hijack
//! the process by inserting their own transaction to initialize the product
//! (for instance, invoking a different factory instance than intended by the
//! originator). To prevent this possibility, the product checks in its
//! `initialize` method that the invoker of the `produce` transaction is the
//! same account as created the product contract instance (i.e. the "owner").
//!
//! Note that typically it is wrong to use the `invoker` of a transaction for
//! authorization, rather than the immediate caller. For instance, a user might
//! invoke some untrusted smart contract, and expect it is not authorized to
//! transfer tokens she holds on another contract. If the token-holding contract
//! used the invoker for authorization, then the untrusted contract could
//! transfer the tokens. In the case of the factory pattern, however, the
//! authorization is for a one-time use (initializing the product contract)
//! and should occur immediately after the product is created. An adversary
//! would have to convince a user to sign a malicious transaction in between the
//! construction and (intended) initialization transactions in order to hijack
//! the product contract. This is hopefully unlikely. Moreover, the effect of
//! such a hijacking should typically be that the product cannot be used as the
//! user intended, but the user would still be able to create another product
//! and have the factory produce that correctly.
//!
//! This security model relies on the fact that none of the initialization of
//! the product occurs in the constructor of the product (the `init` method),
//! but instead is handled by the `initialize` endpoint that is called by the
//! factory. In particular, if any funds or authorization are granted to the
//! product before `initialize` is called, then the consequences and risk of
//! hijacking are more sever. Thus, to adhere to the factory pattern, the
//! product contract must:
//!
//! 1. Always be constructed in an uninitialized state, with no balance,
//! authority or any other state.
//!
//! 2. Only permit the `initialize` update operation while it is in the
//! uninitialized state.
//!
//! 3. On a successful call of `initialize`, transition from the uninitialized
//! state to an initialized state.
//!
//! 4. Never transition back to the uninitialized state.
//!
//! It is important to always consider the risks presented by malicious third
//! parties and to evaluate if any given solution is appropriate to the
//! application at hand.
//!
//! # Alternatives to the factory pattern
//!
//! As mentioned above, the factory pattern is not idiomatic on Concordium, as
//! producing a new contract instance from a factory requires a two-transaction
//! process. The following alternatives may be more suitable for an application.
//!
//! ## Construct the product directly
//! If the factory does not maintain an on-going relationship with the product,
//! then it is generally possible to simply initialize the product entirely in
//! the constructor, removing the separate `initialize` operation entirely. In
//! the example presented here, the factory initializes each product with a
//! unique index, and maintains a map of the products by this index. The
//! `produce` and `initialize` operations are used to establish this
//! relationship.
//!
//! In particular, if the factory contract does not need to update its state
//! after initializing the product, then it serves no purpose. It would be
//! sufficient to construct the product directly in the same way as the factory
//! would have.
//!
//! ## Register the instance with a contract registry
//! In the present example, the factory contract serves as a registry of its
//! products. The factory pattern enables this, as the factory is responsible
//! for initializing each product instance. However, the factory pattern is not
//! in itself necessary for a contract registry. Instead, instances could be
//! constructed directly (as in the previous alternative) and subsequently
//! registered with a registry contract, which maintains an index of the
//! instances registered with it. The registration process could also provide
//! additional initialization information for the contract being registered
//! (such as the index it is assigned by the registry).
//!
//! In the factory pattern, the factory authenticates the uninitialized product
//! instances (checking that they are instances of a particular determined smart
//! contract). A registry could perform similar checks. Alternatively, updating
//! the registry could require authorization by a trusted party that eliminates
//! the need for such checks. This may be useful if the registry is expected to
//! handle instances of multiple different smart contracts.
//!
//! ## A monolithic contract
//! Instead of having separate contract instances for the factory and each
//! product, all of these could be combined in a single monolithic contract. In
//! this model, each product is assigned a virtual address, and the contract
//! maintains a mapping from virtual addresses to the state of each product.
//!
//! For instance, a CIS2 contract can manage multiple NFTs that each have
//! distinct token IDs. Rather than each NFT being in its own contract (that may
//! be created by a factory contract), they are simply handled as part of the
//! state of the overall CIS2 contract. Here, the token ID acts as a virtual
//! address.
//!
//! The main disadvantage of this approach is that the isolation between the
//! states of each product must be enforced by the contract itself. If the state
//! became corrupted (due to a bug in the contract) then it could affect any or
//! all of the encapsulated products. With the factory pattern, the runtime
//! system of the chain enforces isolation. As always, the balance of risks
//! should be considered when choosing the approach for any application.

#![cfg_attr(not(feature = "std"), no_std)]

pub mod factory {
    //! The factory smart contract.

    use concordium_std::*;

    /// The name of the constructor used to create the product contract.
    const PRODUCT_INIT_NAME: &str = "init_product";
    /// The entrypoint for initializing the product contract.
    const PRODUCT_INITIALIZE_ENTRYPOINT: &str = "initialize";

    #[derive(Serial, DeserialWithState)]
    #[concordium(state_parameter = "S")]
    /// The state of the factory contract.
    /// This keeps a record of all of the product contracts.
    pub struct FactoryState<S: HasStateApi = StateApi> {
        /// The index that will be assigned to the next product contract.
        /// Equivalently, the number of product contracts that have been
        /// produced.
        ///
        /// Note, for all practical purposes, using a `u64` to count the
        /// products cannot overflow. In particular, the blockchain does
        /// not allow for more than 2^64 smart contracts.
        next_product: u64,
        /// Index of the product smart contract instances.
        products:     StateMap<u64, ContractAddress, S>,
    }

    /// Errors
    #[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
    pub enum FactoryError {
        /// Failed parsing the parameter.
        #[from(ParseError)]
        ParseParams,
        /// [`produce`] was called with a non-existent product contract.
        /// Or [`view_product`] was called with an index for a non-existent
        /// product.
        NonExistentProduct,
        /// The product was not of the correct module and contract name.
        InvalidProduct,
        /// The product could not be initialized, probably because it is already
        /// initialized.
        InitializeFailed,
    }

    /// Init function that creates a new factory.
    /// The new factory will have no products, and new products will be assigned
    /// indexes starting from 0.
    #[init(contract = "factory")]
    pub fn init(_ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<FactoryState> {
        // Creating `State`
        let state = FactoryState {
            next_product: 0,
            products:     state_builder.new_map(),
        };
        Ok(state)
    }

    /// "Produce" a new instance of the product contract. This does not directly
    /// create the instance, but requires it to be passed as a parameter.
    /// The following checks take place:
    ///
    /// * The parameter *must* be a contract address. Otherwise
    ///   [`FactoryError::ParseParams`] is returned.
    ///
    /// * The supplied contract address *must* point to an existing smart
    ///   contract instance. Otherwise [`FactoryError::NonExistentProduct`] is
    ///   returned.
    ///
    /// * The supplied instance *must* be an instance of the `product` contract
    ///   defined in this module. Otherwise [`FactoryError::InvalidProduct`] is
    ///   returned.
    ///
    /// * The supplied instance *must* be uninitialized. Moreover, the
    ///   preconditions for [`crate::product::initialize`] must be met. (In
    ///   particular, the invoker of this transaction must be the same account
    ///   as created the product instance.) Otherwise
    ///   [`FactoryError::InitializeFailed`] is returned.
    ///
    /// If successful, the product is assigned a fresh index (as part of the
    /// initialization), and is recorded in the factory's index.
    #[receive(
        contract = "factory",
        name = "produce",
        parameter = "ContractAddress",
        mutable,
        return_value = "()",
        error = "FactoryError"
    )]
    pub fn produce(
        ctx: &ReceiveContext,
        host: &mut Host<FactoryState>,
    ) -> Result<(), FactoryError> {
        let product_address = ctx.parameter_cursor().get()?;
        // We can depend upon getting the module reference for our own contract.
        let self_module_ref = host.contract_module_reference(ctx.self_address()).unwrap();
        // Check the product module is the same as our own module.
        let product_module_ref = host
            .contract_module_reference(product_address)
            .or(Err(FactoryError::NonExistentProduct))?;
        ensure_eq!(self_module_ref, product_module_ref, FactoryError::InvalidProduct);
        // Check the product contract name is correct.
        // As this module contains both the factory and product contracts, it is not
        // enough to check just the module reference, because we want to ensure
        // that the would-be product is not an instance of the factory contract.
        let product_name =
            host.contract_name(product_address).or(Err(FactoryError::NonExistentProduct))?;
        ensure_eq!(product_name, PRODUCT_INIT_NAME, FactoryError::InvalidProduct);
        // Update the state
        let state = host.state_mut();
        let next_product = state.next_product;
        state.next_product = next_product + 1;
        let _ = state.products.insert(next_product, product_address);
        // Invoke the initialize entrypoint on the product passing in the index for this
        // product.
        host.invoke_contract(
            &product_address,
            &next_product,
            EntrypointName::new_unchecked(PRODUCT_INITIALIZE_ENTRYPOINT),
            Amount::zero(),
        )
        .or(Err(FactoryError::InitializeFailed))?;
        Ok(())
    }

    /// Get the number of product instances that have been successfully
    /// initialized by this factory.
    #[receive(
        contract = "factory",
        name = "view_product_count",
        return_value = "u64",
        error = "FactoryError"
    )]
    pub fn view_product_count(
        _ctx: &ReceiveContext,
        host: &Host<FactoryState>,
    ) -> Result<u64, FactoryError> {
        Ok(host.state().next_product)
    }

    /// Get the contract address of the product instance for a particular index.
    /// Indexes are assigned sequentially starting from 0.
    #[receive(
        contract = "factory",
        name = "view_product",
        parameter = "u64",
        return_value = "ContractAddress",
        error = "FactoryError"
    )]
    pub fn view_product(
        ctx: &ReceiveContext,
        host: &Host<FactoryState>,
    ) -> Result<ContractAddress, FactoryError> {
        let param: u64 = ctx.parameter_cursor().get()?;
        let ca = host.state().products.get(&param).ok_or(FactoryError::NonExistentProduct)?;
        Ok(ca.to_owned())
    }
}

pub mod product {
    //! The product smart contract.

    use concordium_std::*;

    /// Represents the state of a product after it has been initialized by the
    /// factory.
    #[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
    pub struct Product {
        /// The factory that created the product.
        pub factory: ContractAddress,
        /// The index given to the product by the factory.
        pub index:   u64,
    }

    /// The overall state of a product, which may or may not yet have been
    /// initialized by a factory.
    #[derive(Debug, Serialize, SchemaType, Eq, PartialEq, PartialOrd, Clone)]
    pub enum ProductState {
        /// The product has not yet been initialized by the factory.
        Uninitialized,
        /// The product has been initialised by the factory.
        Initialized(Product),
    }

    /// Errors
    #[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
    pub enum ProductError {
        /// Failed parsing the parameter.
        #[from(ParseError)]
        ParseParams,
        /// The originator of the transaction does not match the owner of the
        /// instance, and thus is not authorized to initialize the contract.
        NotAuthorized,
        /// The product was already initialized.
        AlreadyInitialized,
        /// [`initialize`] was called directly by an account instead of a
        /// factory contract.
        SenderIsAccountAddress,
    }

    /// Construct the product contract in the uninitialized state.
    #[init(contract = "product")]
    pub fn init(_ctx: &InitContext, _state_builder: &mut StateBuilder) -> InitResult<ProductState> {
        Ok(ProductState::Uninitialized)
    }

    /// Initialize the product contract, supplying its index.
    /// The following preconditions are checked:
    ///
    /// * The instance must not have already been initialized. Otherwise,
    ///   [`ProductError::AlreadyInitialized`] is returned.
    ///
    /// * The account invoking the current transaction must be the same account
    ///   that created the instance. Otherwise [`ProductError::NotAuthorized`]
    ///   is returned.
    ///
    /// * The method must be called by another smart contract (the factory). If
    ///   the caller is not a contract, [`ProductError::SenderIsAccountAddress`]
    ///   is returned.
    ///
    /// Note that beyond checking that the caller is a smart contract, this
    /// method does not check further properties of the caller (e.g. that it is
    /// any particular factory smart contract).
    #[receive(
        contract = "product",
        name = "initialize",
        parameter = "u64",
        mutable,
        return_value = "()",
        error = "ProductError"
    )]
    pub fn initialize(
        ctx: &ReceiveContext,
        host: &mut Host<ProductState>,
    ) -> Result<(), ProductError> {
        let state = host.state_mut();
        // Check that the contract has not already been initialized.
        ensure_eq!(*state, ProductState::Uninitialized, ProductError::AlreadyInitialized);
        // Check that the invoker is the owner of the contract.
        ensure_eq!(ctx.invoker(), ctx.owner(), ProductError::NotAuthorized);
        // The index is supplied as a parameter by the factory.
        let index: u64 = ctx.parameter_cursor().get()?;
        // This endpoint should only be called by another smart contract, namely the
        // factory, which we record in the state.
        let factory = match ctx.sender() {
            Address::Contract(ca) => ca,
            _ => Err(ProductError::SenderIsAccountAddress)?,
        };
        // Initialize the state.
        let product = Product {
            index,
            factory,
        };
        *state = ProductState::Initialized(product);
        Ok(())
    }

    #[receive(
        contract = "product",
        name = "view",
        return_value = "ProductState",
        error = "ProductError"
    )]
    pub fn view(
        _ctx: &ReceiveContext,
        host: &Host<ProductState>,
    ) -> Result<ProductState, ProductError> {
        Ok(host.state().to_owned())
    }
}
