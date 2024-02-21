//! An example demonstrating how a factory pattern can be implemented with smart
//! contracts on Concordium.
//!
//! > **Important Note:** The factory pattern is not generally idiomatic on
//! > Concordium. In many cases, a more appropriate solution is to incorporate
//! > the factory and products into a single smart contract instance, rather
//! > than having a separate instance for each product.
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
//! to the `produce` endpoint on the factory. As part of `produce`, the factory
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
//! Since the construction and initialization of the product occur in two
//! separate transactions, it is possible that a third party might try to hijack
//! the process by inserting their own transaction to initialize the product
//! (for instance, invoking a different factory instance than intended by the
//! originator). To prevent this possibility, the product checks in its
//! `initialize` method that the invoker of the `produce` transaction is the
//! same account as created the product contract instance (i.e. the "owner").
//!
//! In this example the factory acts as a registry of all the products it has
//! "produced", assigning each a fresh index and recording the contract address
//! for each. The products are initialized with their index, and also keep a
//! record of the address of the factory contract that produced them. In a
//! practical application, the factory might supply additional paramaters when
//! initializing the products.

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
        /// not (currently) allow for more than 2^64 smart contracts.
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
        /// Or [`view_product`] was called with an indext for a non-existent
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
    #[receive(contract = "factory", name = "produce", parameter = "ContractAddress", mutable)]
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
        if self_module_ref != product_module_ref {
            Err(FactoryError::InvalidProduct)?;
        }
        // Check the product contract name is correct.
        // As this module contains both the factory and product contracts, it is not
        // enough to check just the module reference, because we want to ensure
        // that the would-be product is not an instance of the factory contract.
        let product_name =
            host.contract_name(product_address).or(Err(FactoryError::NonExistentProduct))?;
        if product_name != PRODUCT_INIT_NAME {
            Err(FactoryError::InvalidProduct)?;
        }
        // Invoke the initialize entrypoint on the product passing in the index for this
        // product.
        let next_product = host.state().next_product;
        host.invoke_contract(
            &product_address,
            &next_product,
            EntrypointName::new_unchecked(PRODUCT_INITIALIZE_ENTRYPOINT),
            Amount::zero(),
        )
        .or(Err(FactoryError::InitializeFailed))?;
        // Update the state
        let state = host.state_mut();
        state.next_product = next_product + 1;
        state.products.insert(next_product, product_address);
        Ok(())
    }

    /// Get the number of product instances that have been successfully
    /// initialized by this factory.
    #[receive(contract = "factory", name = "view_product_count")]
    pub fn view_product_count(
        _ctx: &ReceiveContext,
        host: &Host<FactoryState>,
    ) -> Result<u64, FactoryError> {
        Ok(host.state().next_product)
    }

    /// Get the contract address of the product instance for a particular index.
    /// Indexes are assigned sequentially starting from 0.
    #[receive(contract = "factory", name = "view_product", parameter = "u64")]
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
        /// [`initialize`] was not called by a factory contract.
        NotInitializedByFactory,
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
    ///   the caller is not a contract,
    ///   [`ProductError::NotInitializedByFactory`] is returned.
    ///
    /// Note that beyond checking that the caller is a smart contract, this
    /// method does not check further properties of the caller (e.g. that it is
    /// any particular factory smart contract).
    #[receive(contract = "product", name = "initialize", parameter = "u64", mutable)]
    pub fn initialize(
        ctx: &ReceiveContext,
        host: &mut Host<ProductState>,
    ) -> Result<(), ProductError> {
        let state = host.state_mut();
        // Check that the contract has not already been initialized.
        if let ProductState::Initialized(_) = *state {
            Err(ProductError::AlreadyInitialized)?;
        }
        // Check that the invoker is the owner of the contract.
        if ctx.invoker() != ctx.owner() {
            Err(ProductError::NotAuthorized)?;
        }
        // The index is supplied as a parameter by the factory.
        let index: u64 = ctx.parameter_cursor().get()?;
        // This endpoint should only be called by another smart contract, namely the
        // factory, which we record in the state.
        let factory = match ctx.sender() {
            Address::Contract(ca) => ca,
            _ => Err(ProductError::NotInitializedByFactory)?,
        };
        // Initialize the state.
        let product = Product {
            index,
            factory,
        };
        *state = ProductState::Initialized(product);
        Ok(())
    }

    #[receive(contract = "product", name = "view")]
    pub fn view(
        _ctx: &ReceiveContext,
        host: &Host<ProductState>,
    ) -> Result<ProductState, ProductError> {
        Ok(host.state().to_owned())
    }
}
