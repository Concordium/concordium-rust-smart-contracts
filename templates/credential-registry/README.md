This smart contract implements an example on-chain registry for the public
part of verifiable credentials (VCs). The contract follows CIS-4: Credential
Registry Standard.

# Description

The contract keeps track of credentials' public data, allows managing the
VC life cycle. and querying VCs data and status. The intended users are
issuers of VCs, holders of VCs, revocation authorities, and verifiers.

When initializing a contract, the issuer provides a type and a schema
reference for the credentials in the registry. The schema reference points
to a JSON document describing the structure of verifiable credentials in the
registry (attributes and their types). If the issuer wants to issue
verifiable credentials of several types, they can deploy several instances
of this contract with different credential types.

## Issuer's functionality

{% if revocable_by_others %}- register/remove revocation authority keys;{% else %}{% endif %}
- register a new credential;
- revoke a credential;
- update the issuer's metadata;
- update the credential metadata;
- update credential schema reference;
{% if restorable %}- upgrade the contract, set implementors;
- restore (cancel revocation of) a revoked credential.{% else %}- upgrade the contract, set implementors.{% endif %}

## Holder's functionality

- revoke a credential by signing a revocation message.
{% if revocable_by_others %}
## Revocation authority's functionality

Revocation authorities are some entities chosen by the issuer that have
revocation capabilities. Their public keys are registered by the issuer and
a revocation authority signs a revocation message with the corresponding
private key.

- revoke a credential by signing a revocation message.{%endif%}

## Verifier's functionality

- view credential status to verify VC validity;
- view credential data to verify proofs (verifiable presentations) requested
  from holders.
  