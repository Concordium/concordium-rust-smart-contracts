================================
Concordium Token Standard (CTS1)
================================

Abstract
========

An standard interface for both fungible and non-fungible tokens implemented in smart contracts.
The interface provides functions for transferring token ownership, authenticating other address to transfer tokens and for other smart contracts to access token balances.
It allows for off-chain applications to track token balances and authentication.

.. contents:: Table of Contents
   :local:

Specification
=============

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED",  "MAY", and "OPTIONAL" in this document are to be interpreted as described in `RFC 2119<https://datatracker.ietf.org/doc/html/rfc2119>`.


General types and serialization
-------------------------------

``TokenID``
^^^^^^^^^^^

Token Identifier, which combined with the address of the smart contract instance implementing CTS1, forms the globally unique identifier of a token type.
It is serialized as 1 byte which value describes a number of bytes; followed by this number of bytes for the token ID.

- A token ID for a token type SHALL NOT change after a token type have been minted.
- A token ID for a token type SHALL NOT be reused for another token type withing the same smart contract.

``TokenAmount``
^^^^^^^^^^^^^^^

An amount of a token type.
It is represented in WASM as an unsigned integer ``i64`` (8 bytes little endian).

``ReceiveHookName``
^^^^^^^^^^^^^^^^^^^^^^^

A smart contract receive function name.
It is serialized as: the function name byte length is represented by the first 2 bytes, followed this many bytes for the function name.

``ReceiveHookData``
^^^^^^^^^^^^^^^^^^^^^^^

Additional bytes to include when calling a receive function on another smart contract.
It is serialized as: the first 2 bytes encodes the length of the data, followed this many bytes for the data.


``ContractName``
^^^^^^^^^^^^^^^^

A smart contract name.
It is serialized as: the contract name byte length is represented by the first 2 bytes, followed this many bytes for the contract name.

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
In case the first byte is 1: 16 bytes for a contract address, bytes for ``ReceiveHookName`` and ``ReceiveHookData`` is followed.

Contract functions
------------------

A smart contract implementing CTS1 MUST export all of the following functions:


``transfer``
^^^^^^^^^^^^

Executes a list of token transfers.
A transfer is a token ID, an amount of this token ID to be transferred from one address to some other address.

.. Hook to trigger for contract receiver

When transferring tokens to a contract address additional information for a receive function hook to trigger is required.

Parameter
~~~~~~~~~

The parameter is a list of transfers and is serialized as:
1 byte representing the number of transfers followed by the bytes for this number of transfers.
Each transfer is serialized as: a ``TokenID``, a ``TokenAmount``, the token owner address ``Address`` and the receiving address ``Receiver``.

Receive hook parameter
~~~~~~~~~~~~~~~~~~~~~~

The parameter for the receive function hook contains information about the transfer, the name of the token contract and some additional data bytes.
It is serialized as: a ``TokenID``, a ``TokenAmount``, the token owner address ``Address``, the name of the token contract ``ContractName`` and ``ReceiveHookData``

Requirements
~~~~~~~~~~~~

- The list of transfers MUST be executed in order.
- The contract function MUST reject if any of the transfers fails to be executed.
- A transfer MUST fail if:

  - The token balance of the from address is insufficient to do the transfer with error INSUFFICIENT_FUNDS.
  - TokenID is unknown with error: INVALID_TOKEN_ID.
  - Fails to log the Transfer event in the contract logs because the log is full with error LOG_FULL.

- A transfer MUST decrease the balance of the ``from`` address and increase the balance of the ``to`` address or fail.
- A transfer with the same address as ``from`` and ``to`` MUST be executed as a normal transfer.
- A transfer of a token amount zero MUST be executed as a normal transfer.
- A transfer of some amount of a token type MUST only transfer the exact amount of tokens between balances.
- The contract function MUST reject if a contract hook function called when receiving tokens rejects.

``updateOperator``
^^^^^^^^^^^^^^^^^^

Add or remove an address as operator of the address sending this message.

Parameter
~~~~~~~~~

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

Parameter
~~~~~~~~~

The parameter consists of a name of the receive function to callback with the result and a list of token ID and address pairs.
It is serialized as: ``ReceiveFunctionName`` followed by 1 byte for the number of queries and then this number of queries.
A queries is serialized as ``TokenID`` followed by ``Address``.

Callback parameter
~~~~~~~~~~~~~~~~~~

The parameter for the callback receive function is a list of query and token amount pairs.
It is serialized as: 1 byte for the number of query-amount pairs and then this number of pairs.
A query-amount pair is serialized as a ``TokenID``, an address ``Address`` and a ``TokenAmount``.

Requirements
~~~~~~~~~~~~

- The contract function MUST reject if the sender is not a contract address with error CONTRACT_ONLY.
- The contract function MUST reject if any of the queries fail.
- A query MUST fail if:

  - The token ID is unknown with error: INVALID_TOKEN_ID.

Logged events
-------------

The idea of the logged events for this specification is for off-chain applications to be able to track balances and operators without knowledge of the contract specific implementation details.
For this reason it is important to log events in any custom functionality for the token contract, if these modifies balances or operators.

It MUST be safe for off-chain applications to assume a contract implementing this specification and no events logged have zero tokens and no operators enabled for any address.

.. Other events custom to the contract implementation MUST be safe for the off-application to ignore.

Transfer
^^^^^^^^

The event to log for a transfer of some amount of a token type.
A contract function which transfers tokens MUST log a transfer for each of these transfers.

The Transfer event is serialized as: first a byte with the value of 0, followed by the token ID ``TokenID``, an amount of tokens ``TokenAmount``, from address ``Address`` and to address ``Address``.

Mint
^^^^

An event for minting MUST be logged every time a new token is minted. This also applies when introducing new token types and the initial token types and amounts in a contract.
Minting a token with a zero amount is valid.

The Mint event is serialized as: first a byte with the value of 1, followed by the token ID ``TokenID``, an amount of tokens being minted ``TokenAmount`` and the owner address for of the tokens ``Address``.

Burn
^^^^

An event for burning MUST be logged every time an amount of tokens are burned.

Burning a zero amount of a token is allowed.

Summing all of the minted amounts from Mint events and subtracting all of the burned amounts from Burn events for a token type MUST sum up to the total supply for the token type.

The Burn event is serialized as: first a byte with the value of 2, followed by the token ID ``TokenID``, an amount of tokens being burned ``TokenAmount`` and the owner address of the tokens ``Address``.

UpdateOperator
^^^^^^^^^^^^^^

The event to log when updating an operator of some address.

The UpdateOperator event is serialized as: first a byte with the value of 3, followed by a byte which is 0 if an operator is being removed and 1 if an operator is being added, then the owner address updating an operator ``Address`` and an operator address ``Address`` being added or removed.

TokenMetadata
^^^^^^^^^^^^^

The event to log when setting the metadata url for a token type.
It consists of a token ID and an URL for the location of the metadata for this token type with an optional hash of the content.
Logging the TokenMetadata event again with the same token ID, is used to update the metadata location.

The TokenMetadata event is serialized as: first a byte with the value of 4, followed by the token ID ``TokenID``, two bytes for the length of the metadata url and then this many bytes for the url to the metadata.
Lastly a byte to indicate whether a hash of the metadata is included, if it value is 0, then no content hash, if the value is 1 then 32 bytes for a SHA256 hash is followed.

Rejection errors
----------------

A smart contract following this specification MUST reject the specified errors found in this specification with the following error codes:

.. list-table::
  :header-rows: 1

  * - Name
    - Error code
    - Description
  * - INVALID_TOKEN_ID
    - -42000001
    - A provided token ID it not part of this token contract.
  * - INSUFFICIENT_FUNDS
    - -42000002
    - An address balance contains insufficient amount of tokens to complete some transfer of a token.
  * - UNAUTHORIZED
    - -42000003
    - Sender is not the address owning the tokens or an operator of the owning address. Note this can also be used if adding another authentication level on top of the standard.
  * - OPERATOR_IS_SENDER
    - -42000004
    - Sender is updating an operator, where the operator is the same as the sender address.
  * - CONTRACT_ONLY
    - -42000005
    - The sender is not a contract address.

The smart contract implementing this specification MAY introduce custom error codes other than the ones specified in the table above.


Token metadata JSON schema
--------------------------

The token metadata is stored off chain and MUST be a JSON file.

All of the fields in the JSON file are optional, and this specification reserve a number of field names, shown in the table below.

.. list-table:: Token metadata JSON fields
  :header-rows: 1

  * - Property
    - JSON value type [JSON-Schema]
    - Description
  * - ``name`` (optional)
    - string
    - The name to display for the token type.
  * - ``symbol`` (optional)
    - string
    - Short text to display for the token type.
  * - ``decimals`` (optional)
    - number [integer in inclusive range (0, 20)]
    - The number of decimals, when displaying an amount of this token type in a user interface.
  * - ``description`` (optional)
    - string
    - A description for this token type.
  * - ``thumbnail`` (optional)
    - string
    - An thumbnail image URI to display for the asset.
  * - ``display`` (optional)
    - string
    - An image URI to display for the asset.
  * - ``asset`` (optional)
    - URI JSON object
    - An uri to a single asset.
  * - ``assets`` (optional)
    - JSON array of URI JSON objects
    - URI's to a collection of assets.
  * - ``localization`` (optional)
    - JSON object with locales as field names (RFC5646) and field values are URI JSON object to JSON files.
    - URI's to JSON files with localized token metadata.

Optionally a SHA256 hash of the JSON file can be logged with the TokenMetadata event for checking integrity.
Since the metadata json file could contain URIs, a SHA256 hash can optionally be associated with the URI.
To associate a hash with a URI the JSON value is an object

  .. list-table:: URI JSON Object
    :header-rows: 1

    * - Property
      - JSON value type [JSON-Schema]
      - Description
    * - ``uri``
      - string [``uri-reference``]
      - An URI.
    * - ``hash`` (optional)
      - string
      - A SHA256 hash of the URI content encoded as a hex string.


Example token metadata
^^^^^^^^^^^^^^^^^^^^^^

An example of token metadata for a CTS1 implementation wrapping the GTU could be:

.. code-block:: json

  {
    "name": "Wrapped GTU Token",
    "symbol": "wGTU",
    "decimals": 6,
    "description": "A CTS1 token wrapping the Global Transaction Unit",
    "thumbnail": { "uri": "https://location.of/the/thumbnail.png" },
    "localization": {
      "da-DK": {
        "uri": "https://location.of/the/danish/metadata.json",
        "hash": "624a1a7e51f7a87effbf8261426cb7d436cf597be327ebbf113e62cb7814a34b"
      }
    }
  }

The danish localization JSON file could be:

.. code-block:: json

  {
    "description": "CTS1 indpakket GTU"
  }



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
- No error code for receiver hook functions, to allow for more custom errors when receiver is rejecting.
