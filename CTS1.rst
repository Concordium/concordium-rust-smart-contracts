================================
Concordium Token Standard (CTS1)
================================

Status: Draft

Abstract
========

An standard interface for both fungible and non-fungible tokens implemented in smart contracts.
The interface provides functions for transferring token ownership, authenticating other address to transfer tokens and for other smart contracts to access token balances.
It allows for off-chain applications to track token balances and authentication through logged events.
Tokens can have metadata

.. contents:: Table of Contents
   :local:

Specification
=============

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED",  "MAY", and "OPTIONAL" in this document are to be interpreted as described in RFC 2119.


General types and serialization
-------------------------------

.. _CTS-TokenID:

``TokenID``
^^^^^^^^^^^

Token Identifier, which combined with the address of the smart contract instance implementing CTS1, forms the globally unique identifier of a token type.
It is serialized as 1 byte which value describes a number of bytes; followed by this number of bytes for the token ID.

- A token ID for a token type SHALL NOT change after a token type have been minted.
- A token ID for a token type SHALL NOT be reused for another token type withing the same smart contract.

.. _CTS-TokenAmount:

``TokenAmount``
^^^^^^^^^^^^^^^

An amount of a token type.
It is represented in WASM as an unsigned integer ``i64`` (8 bytes little endian).

.. _CTS-ReceiveHookName:

``ReceiveHookName``
^^^^^^^^^^^^^^^^^^^^^^^

A smart contract receive function name.
It is serialized as: the function name byte length is represented by the first 2 bytes, followed this many bytes for the function name.

.. _CTS-ReceiveHookData:

``ReceiveHookData``
^^^^^^^^^^^^^^^^^^^^^^^

Additional bytes to include when calling a receive function on another smart contract.
It is serialized as: the first 2 bytes encodes the length of the data, followed this many bytes for the data.

.. _CTS-ContractName:

``ContractName``
^^^^^^^^^^^^^^^^

A smart contract name.
It is serialized as: the contract name byte length is represented by the first 2 bytes, followed this many bytes for the contract name.

.. _CTS-Address:

``Address``
^^^^^^^^^^^

Is either an account address or a contract address.

It is serialized as: First byte indicates whether it is an account address or a contract address.
In case the first byte is 0: 32 bytes for an account address is followed.
In case the first byte is 1: 16 bytes for a contract address is followed.

.. _CTS-Receiver:

``Receiver``
^^^^^^^^^^^^

The receiving address of a transfer, which is either an account address or a contract address.
In the case of a contract address, additional information such as the name of a receive function and some additional bytes to call on the receiving contract.

It is serialized as: First byte indicates whether it is an account address or a contract address.
In case the first byte is 0 then 32 bytes for an account address is followed.
In case the first byte is 1 then 16 bytes for a contract address, bytes for :ref:`ReceiveHookName` and :ref:`ReceiveHookData` is followed.

.. _CTS-functions:

Contract functions
------------------

A smart contract implementing CTS1 MUST export three functions :ref:`transfer`, :ref:`updateOperator` and :ref:`balanceOf` according to the following description:

.. _CTS-functions-transfer:

``transfer``
^^^^^^^^^^^^

Executes a list of token transfers.
A transfer is a token ID, an amount of this token ID to be transferred from one address to some other address.

When transferring tokens to a contract address additional information for a receive function hook to trigger is required.

Parameter
~~~~~~~~~

The parameter is a list of transfers and is serialized as:
1 byte representing the number of transfers followed by the bytes for this number of transfers.
Each transfer is serialized as: a :ref:`TokenID`, a :ref:`TokenAmount`, the token owner address :ref:`Address` and the receiving address :ref:`Receiver`.

.. _CTS-functions-transfer-receive-hook-parameter:

Receive hook parameter
~~~~~~~~~~~~~~~~~~~~~~

The parameter for the receive function hook contains information about the transfer, the name of the token contract and some additional data bytes.
It is serialized as: a :ref:`TokenID`, a :ref:`TokenAmount`, the token owner address :ref:`Address`, the name of the token contract :ref:`ContractName` and :ref:`ReceiveHookData`

Requirements
~~~~~~~~~~~~

- The list of transfers MUST be executed in order.
- The contract function MUST reject if any of the transfers fails to be executed.
- A transfer MUST fail if:

  - The token balance of the ``from`` address is insufficient to do the transfer with error :ref:`INSUFFICIENT_FUNDS<CTS-rejection-errors>`.
  - TokenID is unknown with error: :ref:`INVALID_TOKEN_ID<CTS-rejection-errors>`.

- A transfer MUST decrease the balance of the ``from`` address and increase the balance of the ``to`` address or fail.
- A transfer with the same address as ``from`` and ``to`` MUST be executed as a normal transfer.
- A transfer of a token amount zero MUST be executed as a normal transfer.
- A transfer of some amount of a token type MUST only transfer the exact amount of tokens between balances.
- A transfer of any amount of a token type to a contract address MUST call receive hook function on the receiving smart contract with a receive hook parameter :ref:`described above<CTS-functions-transfer-receive-hook-parameter>`
- The contract function MUST reject if a receive hook function called on the contract receiving tokens rejects.

.. _CTS-functions-updateOperator:

``updateOperator``
^^^^^^^^^^^^^^^^^^

Add or remove an address as operator of the address sending this message.

Parameter
~~~~~~~~~

The parameter is first a byte indicating whether to remove or add an operator, where if the byte is 0 the sender is removing an operator, if the byte is 1 the sender is adding an operator.
The followed is the operator address :ref:`Address` to add or remove as operator for the sender.

Requirements
~~~~~~~~~~~~

- The contract function MUST reject if the sender address is the same as the operator address with error :ref:`OPERATOR_IS_SENDER<CTS-rejection-errors>`.

.. note::

  Operators are not set per token ID, and an operator can control any token type of the owner address.
  This was chosen to require less on the contract implementation and also simplify off-chain integration.
  If needed a more fine grained authentication system can still exist next to the operators.

.. _CTS-functions-balanceOf:

``balanceOf``
^^^^^^^^^^^^^

Query balances of a list of addresses and token IDs, the result is then send back the sender.

Parameter
~~~~~~~~~

The parameter consists of a name of the receive function to callback with the result and a list of token ID and address pairs.
It is serialized as: :ref:`ReceiveFunctionName` followed by 1 byte for the number of queries and then this number of queries.
A queries is serialized as :ref:`TokenID` followed by :ref:`Address`.

Callback parameter
~~~~~~~~~~~~~~~~~~

The parameter for the callback receive function is a list of query and token amount pairs.
It is serialized as: 1 byte for the number of query-amount pairs and then this number of pairs.
A query-amount pair is serialized as a :ref:`TokenID`, an address :ref:`Address` and a :ref:`TokenAmount`.

Requirements
~~~~~~~~~~~~

- The contract function MUST reject if the sender is not a contract address with error :ref:`CONTRACT_ONLY<CTS-rejection-errors>`.
- The contract function MUST reject if any of the queries fail.
- A query MUST fail if the token ID is unknown with error: :ref:`INVALID_TOKEN_ID<CTS-rejection-errors>`.

Logged events
-------------

The idea of the logged events for this specification is for off-chain applications to be able to track balances and operators without knowledge of the contract specific implementation details.
For this reason it is important to log events in any custom functionality for the token contract, if these modifies balances or operators.

It MUST be safe for off-chain applications to assume a contract implementing this specification and no events logged have zero tokens and no operators enabled for any address.

.. Other events custom to the contract implementation MUST be safe for the off-application to ignore.

Transfer
^^^^^^^^

The event to log for a transfer of some amount of a token type.
A contract function which transfers tokens MUST log a transfer event for each of these transfers.

The Transfer event is serialized as: first a byte with the value of 0, followed by the token ID :ref:`TokenID`, an amount of tokens :ref:`TokenAmount`, from address :ref:`Address` and to address :ref:`Address`.

Mint
^^^^

An event for minting MUST be logged every time a new token is minted. This also applies when introducing new token types and the initial token types and amounts in a contract.
Minting a token with a zero amount is valid.

The Mint event is serialized as: first a byte with the value of 1, followed by the token ID :ref:`TokenID`, an amount of tokens being minted :ref:`TokenAmount` and the owner address for of the tokens :ref:`Address`.

Burn
^^^^

An event for burning MUST be logged every time an amount of tokens are burned.
Burning a zero amount of a token is allowed.

Summing all of the minted amounts from Mint events and subtracting all of the burned amounts from Burn events for a token type MUST sum up to the total supply for the token type.

The Burn event is serialized as: first a byte with the value of 2, followed by the token ID :ref:`TokenID`, an amount of tokens being burned :ref:`TokenAmount` and the owner address of the tokens :ref:`Address`.

UpdateOperator
^^^^^^^^^^^^^^

The event to log when updating an operator of some address.
The UpdateOperator event is serialized as: first a byte with the value of 3, followed by a byte which is 0 if an operator is being removed and 1 if an operator is being added, then the owner address updating an operator :ref:`Address` and an operator address :ref:`Address` being added or removed.

TokenMetadata
^^^^^^^^^^^^^

The event to log when setting the metadata url for a token type.
It consists of a token ID and an URL for the location of the metadata for this token type with an optional SHA256 checksum of the content.
Logging the TokenMetadata event again with the same token ID, is used to update the metadata location and only the most recently logged token metadata event for certain token id should be used to get the token metadata.

The TokenMetadata event is serialized as: first a byte with the value of 4, followed by the token ID :ref:`TokenID`, two bytes for the length of the metadata url and then this many bytes for the url to the metadata.
Lastly a byte to indicate whether a hash of the metadata is included, if it value is 0, then no content hash, if the value is 1 then 32 bytes for a SHA256 hash is followed.

.. _CTS-rejection-errors:

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


Token metadata JSON
-------------------

The token metadata is stored off chain and MUST be a JSON file.

All of the fields in the JSON file are optional, and this specification reserve a number of field names, shown in the table below.

.. list-table:: Token metadata JSON Object
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
    - number [``integer``]
    - The number of decimals, when displaying an amount of this token type in a user interface.
  * - ``description`` (optional)
    - string
    - A description for this token type.
  * - ``thumbnail`` (optional)
    - string
    - An image URI to a small image for displaying the asset.
  * - ``display`` (optional)
    - string
    - An image URI to a large image for displaying the asset.
  * - ``artifact`` (optional)
    - URI JSON object
    - A URI to the token asset.
  * - ``assets`` (optional)
    - JSON array of Token metadata JSON objects
    - Collection of assets.
  * - ``attributes`` (optional)
    - JSON array of Attribute JSON objects
    - Assign a number of attributes to the token type.
  * - ``localization`` (optional)
    - JSON object with locales as field names (RFC5646) and field values are URI JSON object to JSON files.
    - URI's to JSON files with localized token metadata.

Optionally a SHA256 hash of the JSON file can be logged with the TokenMetadata event for checking integrity.
Since the metadata json file could contain URIs, a SHA256 hash can optionally be associated with the URI.
To associate a hash with a URI the JSON value is an object:

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

Attributes are objects with the following fields:

.. list-table:: Attribute JSON object
  :header-rows: 1

  * - Property
    - JSON value type [JSON-Schema]
    - Description
  * - ``type``
    - string
    - Type for the value field of the attribute.
  * - ``name``
    - string
    - Name of the attribute.
  * - ``value``
    - string
    - Value of the attrbute.


Example token metadata: Fungible
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

An example of token metadata for a CTS1 implementation wrapping the GTU could be:

.. code-block:: json

  {
    "name": "Wrapped GTU Token",
    "symbol": "wGTU",
    "decimals": 6,
    "description": "A CTS1 token wrapping the Global Transaction Unit",
    "thumbnail": { "uri": "https://location.of/the/thumbnail.png" },
    "display": { "uri": "https://location.of/the/display.png" },
    "artifact": { "uri": "https://location.of/the/artifact.png" },
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

Example token metadata: Non-fungible
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

An example of token metadata for a NFT could be:

.. code-block:: json

  {
    "name": "Bibi - The Ryan Cat",
    "description": "Ryan cats are lonely creatures travelling the galaxy in search of their ancestors and true inheritance",
    "thumbnail": { "uri": "https://location.of/the/thumbnail.png" },
    "display": { "uri": "https://location.of/the/display.png" },
    "attributes": [{
      "type": "date",
      "name": "Birthday",
      "value": "1629792199610"
    }, {
      "type": "string",
      "name": "Body",
      "value": "Strong"
    }, {
      "type": "string",
      "name": "Head",
      "value": "Round"
    }, {
      "type": "string",
      "name": "Tail",
      "value": "Short"
    }],
    "localization": {
      "da-DK": {
        "uri": "https://location.of/the/danish/metadata.json",
        "hash": "588d7c14883231cfee522479cc66565fd9a50024603a7b8c99bd7869ca2f0ea3"
      }
    }
  }

The danish localization JSON file could be:

.. code-block:: json

  {
    "name": "Bibi - Ryan katten",
    "description": "Ryan katte er ensomme væsner, som rejser rundt i galaxen søgende efter deres forfædre og sande fortid"
  }


Decisions and rationale
=======================

In this section we point out some of the differences from other popular token standards found on other blockchains, and try to reason why this was decided.

Only batched transfers
----------------------

The specification only have a :ref:`transfer` smart contract function which takes list of transfer and no function for a single transfer.
This will result in lower energy cost compared to multiple contract calls and only introduce a small overhead for single transfers.
The reason for not also including a single transfer function, is to have smaller smart contract modules, which in terms lead saving cost on every function call.

No token level approval/allowance like in ERC20 and ERC721
----------------------------------------------------------

This standard only specifies address-level operators and no authentication on per token level.
The main argument is simplicity and to save energy cost on common cases, but other reasons are:

- A token level authentication requires the token smart contract to track more state, which increases the overall energy cost.
- For token smart contracts with a lot of token types, such as a smart contract with a large collection of NFTs, a token level authentication could become very expensive.
- For fungible tokens; approval/allowance introduces an attack vector as `described here<https://docs.google.com/document/d/1YLPtQxZu1UAvO9cZ1O2RPXBbT0mooh4DYKjA_jp-RLM/edit>`.

.. note::

  The specification does not prevent adding more fine-grained authentication, such as a token level authentication.

Receive hook function
---------------------

The specification requires a token receive hook to be called on a smart contract receiving tokens, this will in some cases prevent mistakes such as sending tokens to smart contracts, which do not defined behavior for receiving tokens.
These token could then be lost forever.

The reason for this not being optional is to allow other smart contracts which integrates with a token smart contract to rely on this for functionality.
An auction smart contract could take bids by token transfers directly.

.. warning::

  The smart contract receive hook function could be called by any smart contract and it is up to the integrating contract whether to trust the token contract.

Receive hook function callback argument
---------------------------------------

The name of the receive hook function called on a smart contract receiving tokens is supplied as part of the parameter.
This allows for a smart contract to integrating with a token smart contract to have multiple hooks and leave it to the caller to know which hook they want to trigger.
An auction smart contract could receive the item to auction using one hook and bids on another hook.

Another technical reason is that the name of the smart contract is part of the smart contract receive function name, which means the specification would include a requirement of the smart contract name for other to integrate reliably.

No sender hook function
-----------------------

The FA2 token standard found on Tezos, allows for a hook function to be called on a smart contract sending tokens, such that the contract could reject the transfer on some criteria.
This seems to only make sense, if some operator is transferring tokens from a contract, in which case the sender smart contract might as well contain the logic to transfer the tokens and trigger this directly.

Explicit events for mint and burn
---------------------------------

In ERC20, ERC721 and ERC1155 they use a transfer event from or to the zero address to indicate mint and burn respectively, but since there are no such thing as the zero address on the Concordium blockchain these events are separate.
Making it more explicit, instead of special case transfer events.

No error code for receive hook rejecting
----------------------------------------

The specification could include an error code, for the receive hook function to return if rejecting the token transferred (as seen in the FA2 standard on Tezos).
But we chose to leave this error code up to the receiving smart contract, which allows for more informative error codes.

Adding SHA256 checksum for token metadata event
-----------------------------------------------

A token can optionally include a SHA256 checksum when logging the token metadata event, this is to ensure the integrity of the token metadata.
This checksum can be updated by logging a new event.
