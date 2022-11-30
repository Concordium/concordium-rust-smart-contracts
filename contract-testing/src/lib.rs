use anyhow::anyhow;
use concordium_base::base::{Energy, ExchangeRate};
use concordium_contracts_common::*;
use sha2::{Digest, Sha256};
use std::{
    collections::{
        btree_map::Entry::{Occupied, Vacant},
        BTreeMap, LinkedList,
    },
    path::Path,
};
use wasm_chain_integration::{
    v0,
    v1::{self, ConcordiumAllowedImports, ReturnValue},
    ExecResult, InterpreterEnergy,
};
use wasm_transform::artifact;

pub struct Chain {
    /// The slot time viewable inside the smart contracts.
    /// An error is thrown if this is `None` and the contract tries to
    /// access it.
    slot_time:            Option<SlotTime>,
    /// MicroCCD per Energy.
    micro_ccd_per_energy: ExchangeRate,
    /// Accounts and info about them.
    accounts:             BTreeMap<AccountAddress, AccountInfo>,
    /// Smart contract modules.
    modules: BTreeMap<
        ModuleReference,
        artifact::Artifact<v1::ProcessedImports, artifact::CompiledFunction>,
    >,
    /// Smart contract instances.
    contracts:            BTreeMap<ContractAddress, v1::trie::MutableState>,
    /// Next contract index to use when creating a new instance.
    next_contract_index:  u64,
}

impl Chain {
    pub fn new_with_time(slot_time: SlotTime, energy_per_micro_ccd: ExchangeRate) -> Self {
        Self {
            slot_time: Some(slot_time),
            ..Self::new(energy_per_micro_ccd)
        }
    }

    pub fn new(energy_per_micro_ccd: ExchangeRate) -> Self {
        Self {
            slot_time:            None,
            micro_ccd_per_energy: energy_per_micro_ccd,
            accounts:             BTreeMap::new(),
            modules:              BTreeMap::new(),
            contracts:            BTreeMap::new(),
            next_contract_index:  0,
        }
    }

    pub fn module_deploy<P: AsRef<Path>>(
        &mut self,
        sender: AccountAddress,
        module_path: P,
    ) -> Result<SuccessfulModuleDeployment, DeployModuleError> {
        // Load file
        let module = std::fs::read(module_path)?;

        // Deserialize as wasm module (artifact)
        let artifact = wasm_transform::utils::instantiate_with_metering::<v1::ProcessedImports, _>(
            &ConcordiumAllowedImports {
                support_upgrade: true,
            },
            &module[8..], // skip the 4 version bytes and 4 len bytes
        )
        .map_err(|e| DeployModuleError::InvalidModule(e.to_string()))?;

        // Calculate transaction fee of deployment
        let energy = Energy::from(module.len() as u64 / 10); // From: Concordium/Const/deployModuleCost.hs
        let transaction_fee = self.calculate_energy_cost(energy);

        // Try to subtract cost for account
        match self.accounts.entry(sender) {
            Vacant(_) => return Err(DeployModuleError::AccountDoesNotExist),
            Occupied(mut acc) => {
                let acc = acc.get_mut();
                if acc.balance < transaction_fee {
                    return Err(DeployModuleError::InsufficientFunds);
                }
                acc.balance -= transaction_fee;
            }
        }

        // Save the module
        let module_reference = {
            let mut hasher = Sha256::new();
            hasher.update(module);
            let hash: [u8; 32] = hasher.finalize().into();
            ModuleReference::from(hash)
        };
        self.modules.insert(module_reference, artifact);
        Ok(SuccessfulModuleDeployment {
            module_reference,
            energy,
            transaction_fee,
        })
    }

    pub fn contract_init(
        &mut self,
        sender: AccountAddress,
        module: ModuleReference,
        contract_name: ContractName,
        parameter: ContractParameter,
        amount: Amount,
        energy_limit: Energy,
    ) -> Result<SuccessfulContractInit, ContractInitError> {
        // Lookup artifact
        let artifact = self
            .modules
            .get(&module)
            .ok_or_else(|| ContractInitError::ModuleDoesNotExist)?;
        // Get the account and check that it has sufficient balance to pay for the
        // energy.
        let account_info = self
            .accounts
            .get(&sender)
            .ok_or_else(|| ContractInitError::AccountDoesNotExist)?;
        if account_info.balance < self.calculate_energy_cost(energy_limit) {
            return Err(ContractInitError::InsufficientFunds);
        }
        // Construct the context.
        let init_ctx = InitContextOpt {
            metadata:        ChainMetadataOpt {
                slot_time: self.slot_time,
            },
            init_origin:     sender,
            sender_policies: account_info.policies.clone(),
        };
        // Initialize contract
        let loader = v1::trie::Loader::new(&[][..]);
        let res = v1::invoke_init(
            artifact,
            init_ctx,
            v1::InitInvocation {
                amount,
                init_name: contract_name.get_chain_name(),
                parameter: &parameter.0,
                energy: InterpreterEnergy {
                    // TODO: Why do we have two separate energy types?
                    energy: energy_limit.energy,
                },
            },
            false,
            loader,
        )
        .map_err(|e| ContractInitError::StringInitError(e.to_string()))?;
        // Charge account for cost
        let (res, transaction_fee) = match res {
            v1::InitResult::Success {
                logs,
                return_value: _, /* Ignore return value for now, since our tools do not support
                                  * it for inits, currently. */
                remaining_energy,
                state,
            } => {
                let contract_address = self.create_contract_address();
                let energy_used = Energy::from(energy_limit.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);

                // Save the state
                self.contracts.insert(contract_address, state); // Ignore the return value since we created a new contract address for this.

                (
                    Ok(SuccessfulContractInit {
                        contract_address,
                        logs,
                        energy_used,
                        transaction_fee,
                    }),
                    transaction_fee,
                )
            }
            v1::InitResult::Reject {
                reason,
                return_value,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_limit.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);
                (
                    Err(ContractInitError::ValidChainError(
                        FailedContractInteraction::Reject {
                            reason,
                            return_value,
                            energy_used,
                            transaction_fee,
                            logs: v0::Logs {
                                // TODO: Get logs on failures.
                                logs: LinkedList::new(),
                            },
                        },
                    )),
                    transaction_fee,
                )
            }
            v1::InitResult::Trap {
                error,
                remaining_energy,
            } => {
                let energy_used = Energy::from(energy_limit.energy - remaining_energy);
                let transaction_fee = self.calculate_energy_cost(energy_used);
                (
                    Err(ContractInitError::ValidChainError(
                        FailedContractInteraction::Trap {
                            error,
                            energy_used,
                            transaction_fee,
                            logs: v0::Logs {
                                // TODO: Get logs on failures.
                                logs: LinkedList::new(),
                            },
                        },
                    )),
                    transaction_fee,
                )
            }
            v1::InitResult::OutOfEnergy => {
                let transaction_fee = self.calculate_energy_cost(energy_limit);
                (
                    Err(ContractInitError::ValidChainError(
                        FailedContractInteraction::OutOFEnergy {
                            energy_used: energy_limit,
                            transaction_fee,
                            logs: v0::Logs {
                                // TODO: Get logs on failures.
                                logs: LinkedList::new(),
                            },
                        },
                    )),
                    transaction_fee,
                )
            }
        };
        // Charge the account.
        // We have to get the account info again because of the borrow checker.
        self.accounts
            .get_mut(&sender)
            .ok_or_else(|| ContractInitError::AccountDoesNotExist)?
            .balance -= transaction_fee;
        res
    }

    /// Can we get the return value here?
    pub fn contract_update(
        &mut self,
        _sender: AccountAddress,
        _address: ContractAddress,
        _entrypoint: EntrypointName,
        _parameter: ContractParameter,
        _amount: Amount,
        _energy: Energy,
    ) -> Result<SuccessfulContractUpdate, FailedContractInteraction> {
        todo!()
    }

    /// If `None` is provided, address 0 will be used, which will have
    /// sufficient funds.
    pub fn contract_invoke(
        &mut self,
        _sender: Option<AccountAddress>,
        _address: ContractAddress,
        _entrypoint: EntrypointName,
        _parameter: ContractParameter,
        _amount: Amount,
        _energy: Option<Energy>, // Defaults to 100000 if `None`.
    ) -> Result<SuccessfulContractUpdate, FailedContractInteraction> {
        todo!()
    }

    /// Create an account. Will override existing account if already present.
    pub fn create_account(&mut self, account: AccountAddress, account_info: AccountInfo) {
        self.accounts.insert(account, account_info);
    }

    /// Creates a contract address with an index one above the highest
    /// currently used. Next call to `contract_init` will skip this
    /// address.
    pub fn create_contract_address(&mut self) -> ContractAddress {
        let index = self.next_contract_index;
        let subindex = 0;
        self.next_contract_index += 1;
        ContractAddress::new(index, subindex)
    }

    pub fn set_slot_time(&mut self, slot_time: SlotTime) { self.slot_time = Some(slot_time); }

    pub fn set_energy_per_micro_ccd(&mut self, energy_per_micro_ccd: ExchangeRate) {
        self.micro_ccd_per_energy = energy_per_micro_ccd;
    }

    /// Returns the balance of an account if it exists.
    pub fn account_balance(&self, address: AccountAddress) -> Option<Amount> {
        self.accounts.get(&address).and_then(|ai| Some(ai.balance))
    }

    pub fn calculate_energy_cost(&self, energy: Energy) -> Amount {
        Amount::from_micro_ccd(
            energy.energy * self.micro_ccd_per_energy.numerator()
                / self.micro_ccd_per_energy.denominator(),
        )
    }
}

/// A chain metadata with an optional field.
/// Used when simulating contracts to allow the user to only specify the
/// necessary context fields.
/// The default value is `None` for all `Option` fields.
pub(crate) struct ChainMetadataOpt {
    slot_time: Option<SlotTime>,
}

impl v0::HasChainMetadata for ChainMetadataOpt {
    fn slot_time(&self) -> ExecResult<SlotTime> {
        unwrap_ctx_field(self.slot_time, "metadata.slotTime")
    }
}

/// An init context with optional fields.
/// Used when simulating contracts to allow the user to only specify the
/// context fields used by the contract.
/// The default value is `None` for all `Option` fields and the default of
/// `ChainMetadataOpt` for `metadata`.
pub(crate) struct InitContextOpt {
    metadata:        ChainMetadataOpt,
    init_origin:     AccountAddress,
    sender_policies: Option<v0::OwnedPolicyBytes>,
}

impl v0::HasInitContext for InitContextOpt {
    type MetadataType = ChainMetadataOpt;

    fn metadata(&self) -> &Self::MetadataType { &self.metadata }

    fn init_origin(&self) -> ExecResult<&AccountAddress> { Ok(&self.init_origin) }

    fn sender_policies(&self) -> ExecResult<&[u8]> {
        unwrap_ctx_field(
            self.sender_policies.as_ref().map(Vec::as_ref),
            "senderPolicies",
        )
    }
}

// Error handling when unwrapping.
fn unwrap_ctx_field<A>(opt: Option<A>, name: &str) -> ExecResult<A> {
    match opt {
        Some(v) => Ok(v),
        None => Err(anyhow!(
            "Missing field '{}' in the context. Make sure to provide all the fields that the \
             contract uses.",
            name,
        )),
    }
}

pub struct AccountInfo {
    /// The account balance. TODO: Do we need the three types of balances?
    pub balance: Amount,
    /// Optional test policies.
    policies:    Option<v0::OwnedPolicyBytes>,
}

impl AccountInfo {
    pub fn new(balance: Amount) -> Self {
        Self {
            balance,
            policies: None,
        }
    }
}

pub enum ContractInitError {
    /// Initialization failed for a reason that also exists on the chain.
    ValidChainError(FailedContractInteraction),
    /// TODO: Can we get a better error than the anyhow?
    StringInitError(String),
    /// Module has not been deployed in test environment.
    ModuleDoesNotExist,
    /// Account has not been created in test environment.
    AccountDoesNotExist,
    /// The account does not have enough funds to pay for the energy.
    InsufficientFunds,
}

#[derive(Debug)]
pub enum FailedContractInteraction {
    Reject {
        reason:          i32,
        return_value:    ReturnValue,
        energy_used:     Energy,
        transaction_fee: Amount,
        /// Logs emitted before the interaction failed. Logs from failed
        /// updates are not stored on the chain, but can be useful for
        /// debugging.
        logs:            v0::Logs,
    },
    Trap {
        error:           anyhow::Error,
        energy_used:     Energy,
        transaction_fee: Amount,
        /// Logs emitted before the interaction failed. Logs from failed
        /// updates are not stored on the chain, but can be useful for
        /// debugging.
        logs:            v0::Logs,
    },
    OutOFEnergy {
        energy_used:     Energy,
        transaction_fee: Amount,
        /// Logs emitted before the interaction failed. Logs from failed
        /// updates are not stored on the chain, but can be useful for
        /// debugging.
        logs:            v0::Logs,
    },
}

#[derive(Debug)]
pub struct ContractError(Vec<u8>);

// TODO: Can we get Eq for this when using io::Error?
// TODO: Should this also have the energy used?
#[derive(Debug)]
pub enum DeployModuleError {
    ReadFileError(std::io::Error),
    InvalidModule(String),
    InsufficientFunds,
    AccountDoesNotExist,
}

impl From<std::io::Error> for DeployModuleError {
    fn from(e: std::io::Error) -> Self { DeployModuleError::ReadFileError(e) }
}

impl ContractError {
    pub fn deserial<T: Deserial>(&self) -> Result<T, ParsingError> { todo!() }
}

#[derive(PartialEq, Eq, Debug)]
pub struct Event(String);

#[derive(PartialEq, Eq, Debug)]
pub enum ChainEvent {
    Interrupted {
        address: ContractAddress,
        events:  Vec<Event>,
    },
    Resumed {
        address: ContractAddress,
        success: bool,
    },
    Upgraded {
        address: ContractAddress,
        from:    ModuleReference,
        to:      ModuleReference,
    },
    Updated {
        address:    ContractAddress,
        contract:   OwnedContractName,
        entrypoing: OwnedEntrypointName,
        amount:     Amount,
    },
}

pub struct SuccessfulContractUpdate {
    /// Host events that occured. This includes interrupts, resumes, and
    /// upgrades.
    pub host_events:     Vec<ChainEvent>,
    pub transfers:       Vec<(AccountAddress, Amount)>,
    /// Energy used.
    pub energy:          Energy,
    /// Cost of transaction.
    pub transaction_fee: Amount,
    /// The returned value.
    pub return_value:    ContractReturnValue,
}

#[derive(Debug, PartialEq, Eq)]
pub struct SuccessfulModuleDeployment {
    pub module_reference: ModuleReference,
    pub energy:           Energy,
    /// Cost of transaction.
    pub transaction_fee:  Amount,
}

#[derive(Debug)]
pub struct SuccessfulContractInit {
    /// The address of the new instance.
    pub contract_address: ContractAddress,
    /// Logs produced during initialization.
    pub logs:             v0::Logs,
    /// Energy used.
    pub energy_used:      Energy,
    /// Cost of transaction.
    pub transaction_fee:  Amount,
}

pub struct ContractReturnValue(Vec<u8>);

#[derive(Debug, PartialEq, Eq)]
pub enum ParsingError {
    /// Thrown by `deserial` on failure.
    ParsingFailed,
}

impl ContractReturnValue {
    pub fn deserial<T: Deserial>(&self) -> Result<T, ParsingError> { todo!() }
}

pub struct ContractParameter(pub Vec<u8>);

impl ContractParameter {
    pub fn empty() -> Self { Self(Vec::new()) }

    pub fn from_bytes(bytes: Vec<u8>) -> Self { Self(bytes) }

    // TODO: add version with serde json
    pub fn from_typed<T: Serial>(parameter: &T) -> Self { Self(to_bytes(parameter)) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deploying_valid_module_works() {
        let mut chain = Chain::new(ExchangeRate::new_unchecked(2404, 1));
        let acc_0 = AccountAddress([0; 32]);
        let initial_balance = Amount::from_ccd(10000);
        chain.create_account(acc_0, AccountInfo::new(initial_balance));

        let res = chain
            .module_deploy(acc_0, "icecream/icecream.wasm.v1") // TODO: Add wasm files to the repo for tests.
            .expect("Deploying valid module should work");

        assert_eq!(chain.accounts.len(), 1);
        assert_eq!(chain.modules.len(), 1);
        assert_eq!(
            chain.account_balance(acc_0),
            Some(initial_balance - res.transaction_fee)
        );
    }
}
