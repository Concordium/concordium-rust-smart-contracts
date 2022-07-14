# Settlement Layer for Off-Chain Transfers

An example implementation of an optimistic settlement layer for off-chain transactions.

 **Warning**
 This contract is is **UNSUITABLE FOR DEPLOYMENT**, and **PROVIDED AS Proof-Of-Concept ONLY**.

# Description
This contract implements a simple settlement mechanism for off-chain payments. It is an example of so-called "rollups" since it allows to roll multiple off-chain transaction up into a single on-chain settlement transaction (and thereby save transaction fees).
The intended use of the contract is as follows:
 * The smart contract is initialized by appointing a "judge" and a "validator", and setting a "time to finality" duration.
 * Users deposit a collateral to the smart contract. This adds the deposited amount to the available balance in the balance sheet of the smart contract.
 * Afterwards, users can transact off-chain using their deposited collateral as balance.
 * Once users are done with their off-chain transactions, the validator can settle the transactions by adding a settlement to the contract. A settlement is described by a transfer, i.e.,  addresses and amounts specifying which addresses have to pay which amounts and which addresses receive which amounts, respectively. Settlements can only be added by the validator to prevent DoS attacks.
 * After a settlement, users can already (optimistically) use the updated balances from that settlement off-chain and in future settlements. Withdrawing received amounts, however, is only possible after the settlement was finalized.
 * If users object to a published settlement, they can off-chain complain to the judge. If the judge deems a settlement invalid before it has been finalized, the judge can veto it.
 * Settlements that have not been vetoed for the "time to finality" duration become finalized and cannot be reverted anymore.
 * The smart contract can be called by anyone to execute all finalized settlements and to update the balance sheet accordingly. 
 * Users can withdraw funds from the smart contract. The maximal allowed amount to withdraw corresponds to the worst-case amount that is guaranteed to be available no matter which outstanding settlements are vetoed.
