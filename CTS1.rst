================================
Concordium Token Standard (CTS1)
================================

Abstract
========

.. contents:: Table of Contents
   :local:

Introduction
============



Specification
=============

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED",  "MAY", and "OPTIONAL" in this document are to be interpreted as described in `RFC 2119<https://datatracker.ietf.org/doc/html/rfc2119>`.


General types and serialization
-------------------------------

``TokenID``
^^^^^^^^^^^

Token Identifier, which combined with the address of the smart contract instance implementing CTS1, forms the unique identifier of a token type.
It is represented in WASM as an integer ``i64``.


``TokenAmount``
^^^^^^^^^^^^^^^

An amount of a token type.
It is represented in WASM as an unsigned integer ``i64``.

``ReceiveFunctionName``
^^^^^^^^^^^^^^^^^^^^^^^

A smart contract receive function name.
It is serialized as: the function name byte length is represented by the first 2 bytes, followed this many bytes for the function name.

``ReceiveFunctionData``
^^^^^^^^^^^^^^^^^^^^^^^

Additional bytes to include when calling a receive function on another smart contract.
It is serialized as: the first 2 bytes encodes the length of the data, followed this many bytes for the data.


``Address``
^^^^^^^^^^^

Is either an account address or a contract address.

It is serialized as: First byte indicates whether it is an account address or a contract address.
In case the first byte is 0: 32 bytes for an account address is followed.
In case the first byte is 1: 16 bytes for a contract address is followed.

``Receiver``
^^^^^^^^^^^^

The receiving address of a transfer, which is either an account address or a contract address.
In the case of a contract address, additional information such as the name of a receive function and some additional bytes to call on the receiving contract.

It is serialized as: First byte indicates whether it is an account address or a contract address.
In case the first byte is 0: 32 bytes for an account address is followed.
In case the first byte is 1: 16 bytes for a contract address, bytes for ``ReceiveFunctionName`` and ``ReceiveFunctionData`` is followed.


Contract functions
------------------

A smart contract implementing CTS1 MUST export all of the following functions:


``transfer``
^^^^^^^^^^^^

Executes a list of token transfers.
A transfer is a token ID, an amount of this token ID to be transferred from one address to some other address.

.. Hook to trigger for contract receiver

When transferring tokens to a contract address additional information for a receive function to trigger is required.

Parameter
~~~~~~~~~

.. Parameter in Rust? and the serialization
.. u8 sizelength for the list of transfers


The parameter is a list of transfers and is serialized as:
1 byte representing the number of transfers followed by the bytes for this number of transfers.
Each transfer is serialized as: a ``TokenID``, a ``TokenAmount``, the token owner address ``Address`` and the receiving address ``Receiver``.

.. Possible rejections

Requirements
~~~~~~~~~~~~

- The list of transfers MUST be executed in order.
- The contract function MUST reject if any of the transfers fails to be executed. A transfer will fail if:

  - The token balance of the from address is insufficient to do the transfer with error INSUFFICIENT_FUNDS.
  - TokenID is unknown with error: INVALID_TOKEN_ID.
  - Fails to log the Transfer event in the contract logs because the log is full with error LOG_FULL.

- A transfer MUST decrease the balance of the ``from`` address and increase the balance of the ``to`` address or fail.
- A transfer with the same address as ``from`` and ``to`` MUST be executed as a normal transfer.
- A transfer of a token amount zero MUST be executed as a normal transfer.
- A transfer of some amount of a token type MUST only transfer the exact amount of tokens between balances.

.. TODO: reject if the receiver rejects

``updateOperator``
^^^^^^^^^^^^^^^^^^

Add or remove an address as operator of the address sending this message.

The parameter is first a byte indicating whether to remove or add an operator, where if the byte is 0 the sender is removing an operator, if the byte is 1 the sender is adding an operator.
The followed is the operator address `Address` to add or remove as operator for the sender.

Requirements
~~~~~~~~~~~~

- The contract function MUST reject if:

  - The sender address is the same as the operator address with error OPERATOR_IS_SENDER.
  - Fails to log the UpdateOperator event because the log is full with error LOG_FULL.

.. note::

  Operators are not set per token ID, and an operator can control any token type of the owner address.
  This was chosen to require less on the contract implementation and also simplify off-chain integration.
  If needed a more fine grained authentication system can still exist next to the operators.


``balanceOf``
^^^^^^^^^^^^^

Query balances of a list of addresses and token IDs, the result is then send back the sender.

Requirements
~~~~~~~~~~~~

- The contract function MUST reject if:

  - The sender is not a contract address.

.. TODO:

.. u8 sizelength for the list of queries


Logged events
-------------

The idea of the logged events for this specification is for off-chain applications to be able to track balances and operators without knowledge of the contract implementation details.
For this reason it is important to log events in any custom functionality for the token contract, if these modifies balances or operators.

It MUST be safe for off-chain applications to assume a contract implementing this specification and no events logged have zero tokens and no operators enabled for any address.

.. Other events custom to the contract implementation MUST be safe for the off-application to ignore.

Transfer
^^^^^^^^



UpdateOperator
^^^^^^^^^^^^^^

Mint
^^^^

An event for minting MUST be logged every time a new token is minted. This also applies when introducing new token types and the initial token types and amounts in a contract.
Minting a token with a zero amount is valid.

Burn
^^^^

Burning a zero amount of a token is allowed.

Summing all of the minted amounts and subtracting all of the burned amounts for a token type MUST sum up to the total supply for the token type.

TokenMetadata
^^^^^^^^^^^^^

Logs a ``TokenID`` and an URI for the location of the metadata for this token.


Rejection errors
----------------

- INSUFFICIENT_FUNDS
- UNAUTHORIZED
- INVALID_TOKEN_ID
- LOG_FULL
- OPERATOR_IS_SENDER

Token Metadata
--------------

.. JSON format
.. fungible: name, symbol, decimals,
.. non-fungible: name


Differences from other standards
================================

ERC20
-----

- No approval/allowance functions.
- Added receiver hook, which is mandatory.
- Support multiple tokens per contract.
- Batched transfers.
- Added operators per address.
- Explicit events for minting and burning.

ERC721
------

- No approval/allowance functions.
- Added receiver hook, which is mandatory (corresponding to safeTransferFrom).
- Only "safeTransferFrom" to transfer.
- Batched transfers.
- Explicit events for minting and burning.

ERC1155
-------

- Only batched transfers, each with their own sender and receiver.
- No TransferBatch event.
- Receiver hook function name is not part of the specification.
- Explicit events for minting and burning.

FA2
---

- Mandatory receiver hook, but the receive function name is not part of the specification.
- No sender hook.
- Mandatory operators.
- Updating operators is not batched.
- Operator for accounts, not scoped to tokens.
