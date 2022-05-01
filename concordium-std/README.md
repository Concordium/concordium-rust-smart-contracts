A standard library providing a high-level interface for writing smart contracts
for the Concordium blockchain in the Rust programming language.

Links:
- [Documentation](https://docs.rs/concordium-std/latest/concordium_std/)
- [Crates.io](https://crates.io/crates/concordium-std)


## For maintainers

### High-level design of the library

The library aims to provide an easy to use API to use the chain API, as well as
to ensure that users do not make mistakes. There are two kinds of API that are
exposed by the library. The high-level API which sacrifices some performance and
code size but almost allows the users to pretend that the contract state is an
in-memory state, as opposed to an external database, which is what it is in
reality. The low-level API exposes essentially the API that the chain provides,
albeit in a Rust-like manner, so that users do not have to deal with pointers
directly.

The design of the high-level API uses Rust features extensively to prevent
errors, and it assumes that the low-level API is not used at the same time. That
is, the high-level API maintains invariants that can be broken by using the
low-level API. The invariants are maintained by a combination of encapsulation
(i.e., hiding implementation details) and the type system, including extensive
use of lifetimes.

The low-level API exposes a key-value store, which is also the interface exposed
by the chain. Keys are arbitrary byte arrays, and values are byte arrays. The
API is structured around **entries**. When looking up a key an entry is
returned. This entry can then be read and written, using the Read and Write traits.

The high-level API is structured around an "allocator". It exposes three
high-level collections
- a map
- a set
- a "box", i.e., a value behind an indirection.

Nested maps are supported, as well as sets as values inside maps. 

The high-level API works not with byte arrays directly, but with normal structured Rust
types. Serialization of these types to byte arrays (both for keys and for
values) is handled automatically. The API maintains the invariant that if a
value of type T is stored, then it can later be retrieved and deserialized. This
can be violated by the use of the low-level API, since that can be used to write
arbitrary data at arbitrary keys.

The second invariant that is maintained by the high-level API is that the
structure of the map cannot be modified (that is, no insertions or deletions)
while there is an active iterator over the map. This is achieved via lifetimes,
and the fact that mutable references in Rust are unique, and cannot exist
alongside immutable references (to the same object, see lifetime passthrough for
details) in a similar style to how it is achieved for standard Rust collections,
e.g., BTreeMap. This restriction is necessary since the API exposed by the node
does not allow modification of the part of the tree that is iterated over.

These invariants make it so that in many places in the code we abort the program
if an operation might fail, but is ensured by the invariant. For example, when
looking up a value in a map, we assume that deserialization cannot fail.

Another noteworthy item is the use of `Drop` to ensure data is written to the
contract state. The concrete case here is modifications of entries. When, e.g.,
looking we look up an entry in the map, we may then get a `&mut` reference to
the value stored inside the entry. This can then be used to modify the value.
However all of this happens in-memory and at some point must be written to the
actual contract state. One option would have been to require the user to use a
function such as `commit` to achieve this, however this is very error prone,
especially in light of the API which looks very close to the normal collections
API. Thus we use the `Drop` implementation to commit the changes to the contract
state. There are a few optimizations, so that we avoid this writing to contract
state in cases where it is clear no changes were made. But this is not very
precise (it is an overapproximation, i.e., it will often deem it to be
modified), and one should generally not acquire `&mut` references if one does
not attempt to write to the state.

This use of Drop does rely on the second invariant listed above, that
overlapping modifications of the map are not allowed due to lifetime
restrictions. If this was not the case we would risk having inconsistent views
of the state, with the value in memory being different from the value looked up.

### High-level API layout

The root of the high-level state is stored at the empty key, i.e., at `&[]`.
This will typically be a Rust struct, or some other structured type. Inside this
there might be maps or sets, or boxes. These are allocated via the *allocator*.
The allocator determines the next free location to store the map. The allocator
itself must be stored in the contract state, and it is stored at location
`[0,0,0,0,0,0,0,0]`. The value stored at this location is a 64-bit integer which
is interpreted as the location (in little endian bytes). Creating a new map
looks up the allocator value, and updates it.

The high-level API relies on it being the only one that is updating this
allocator. **Modifying the value via other methods will lead to unpredictable
results.**

Thus each map (and set) is associated with a location `ℓ`, a 64-bit integer. A
key-value pair (K, V) in the map is then stored at key (in the contract state)
that is constructed by combining `ℓ` (in little endian) together with the
serialization of `K`.
