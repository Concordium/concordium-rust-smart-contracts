use crate::{
    marker::PhantomData, mem, Deletable, Deserial, DeserialWithState, Get, HasStateApi,
    ParseResult, Read, Serial, Serialize, StateItemPrefix, StateMap, StateRef, StateRefMut,
    UnwrapAbort, Write, STATE_ITEM_PREFIX_SIZE,
};

/// An ordered map based on [B-Tree](https://en.wikipedia.org/wiki/B-tree), where
/// each node is stored separately in the low-level key-value store.
///
/// It can be seen as an extension adding tracking of the keys ordering on top
/// of [`StateMap`] to provide functions such as [`higher`](Self::higher) and
/// [`lower`](Self::lower). This results in some overhead when inserting and
/// deleting entries from the map compared to using [`StateMap`].
///
/// | Operation                                       | Performance   |
/// |-------------------------------------------------|---------------|
/// | [`get`](Self::get) / [`get_mut`](Self::get_mut) | O(k)          |
/// | [`insert`](Self::insert)                        | O(k + log(n)) |
/// | [`remove`](Self::remove)                        | O(k + log(n)) |
/// | [`higher`](Self::higher)/[`lower`](Self::lower) | O(k + log(n)) |
///
/// Where `k` is the byte size of the serialized keys and `n` is the number of
/// entries in the map.
///
/// ## Type parameters
///
/// The map `StateBTreeMap<K, V, S, M>` is parametrized by the types:
/// - `K`: Keys used in the map. Most operations on the map require this to
///   implement [`Serialize`](crate::Serialize). Keys cannot contain references
///   to the low-level state, such as types containing [`StateBox`],
///   [`StateMap`] and [`StateSet`].
/// - `V`: Values stored in the map. Most operations on the map require this to
///   implement [`Serial`](crate::Serial) and
///   [`DeserialWithState<S>`](crate::DeserialWithState).
/// - `S`: The low-level state implementation used, this allows for mocking the
///   state API in unit tests, see
///   [`TestStateApi`](crate::test_infrastructure::TestStateApi).
/// - `M`: A `const usize` determining the _minimum degree_ of the B-tree.
///   _Must_ be a value of `2` or above for the tree to work. This can be used
///   to tweak the height of the tree vs size of each node in the tree. The
///   default is set based on benchmarks.
///
/// ## Usage
///
/// New maps can be constructed using the
/// [`new_btree_map`][StateBuilder::new_btree_map] method on the
/// [`StateBuilder`].
///
/// ```
/// # use concordium_std::*;
/// # use concordium_std::test_infrastructure::*;
/// # let mut state_builder = TestStateBuilder::new();
/// /// In an init method:
/// let mut map1 = state_builder.new_btree_map();
/// # map1.insert(0u8, 1u8); // Specifies type of map.
///
/// # let mut host = TestHost::new((), state_builder);
/// /// In a receive method:
/// let mut map2 = host.state_builder().new_btree_map();
/// # map2.insert(0u16, 1u16);
/// ```
///
/// ### **Caution**
///
/// `StateBTreeMap`s must be explicitly deleted when they are no longer needed,
/// otherwise they will remain in the contract's state, albeit unreachable.
///
/// ```no_run
/// # use concordium_std::*;
/// struct MyState<S: HasStateApi = StateApi> {
///     inner: StateBTreeMap<u64, u64, S>,
/// }
/// fn incorrect_replace(state_builder: &mut StateBuilder, state: &mut MyState) {
///     // The following is incorrect. The old value of `inner` is not properly deleted.
///     // from the state.
///     state.inner = state_builder.new_btree_map(); // ⚠️
/// }
/// ```
/// Instead, either the map should be [cleared](StateBTreeMap::clear) or
/// explicitly deleted.
///
/// ```no_run
/// # use concordium_std::*;
/// # struct MyState<S: HasStateApi = StateApi> {
/// #    inner: StateBTreeMap<u64, u64, S>
/// # }
/// fn correct_replace(state_builder: &mut StateBuilder, state: &mut MyState) {
///     state.inner.clear_flat();
/// }
/// ```
/// Or alternatively
/// ```no_run
/// # use concordium_std::*;
/// # struct MyState<S: HasStateApi = StateApi> {
/// #    inner: StateBTreeMap<u64, u64, S>
/// # }
/// fn correct_replace(state_builder: &mut StateBuilder, state: &mut MyState) {
///     let old_map = mem::replace(&mut state.inner, state_builder.new_btree_map());
///     old_map.delete()
/// }
/// ```
pub struct StateBTreeMap<K, V, S, const M: usize = 8> {
    pub(crate) map:         StateMap<K, V, S>,
    pub(crate) ordered_set: StateBTreeSet<K, S, M>,
}

impl<const M: usize, K, V, S> StateBTreeMap<K, V, S, M> {
    /// Insert a key-value pair into the map.
    /// Returns the previous value if the key was already in the map.
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        S: HasStateApi,
        K: Serialize + Ord,
        V: Serial + DeserialWithState<S>, {
        let old_value_option = self.map.insert_borrowed(&key, value);
        if old_value_option.is_none() && !self.ordered_set.insert(key) {
            // Inconsistency between the map and ordered_set.
            crate::trap();
        }
        old_value_option
    }

    /// Remove a key from the map, returning the value at the key if the key was
    /// previously in the map.
    ///
    /// *Caution*: If `V` is a [StateBox], [StateMap], then it is
    /// important to call [`Deletable::delete`] on the value returned when
    /// you're finished with it. Otherwise, it will remain in the contract
    /// state.
    #[must_use]
    pub fn remove_and_get(&mut self, key: &K) -> Option<V>
    where
        S: HasStateApi,
        K: Serialize + Ord,
        V: Serial + DeserialWithState<S> + Deletable, {
        let v = self.map.remove_and_get(key);
        if v.is_some() && !self.ordered_set.remove(key) {
            // Inconsistency between the map and ordered_set.
            crate::trap();
        }
        v
    }

    /// Remove a key from the map.
    /// This also deletes the value in the state.
    pub fn remove(&mut self, key: &K)
    where
        S: HasStateApi,
        K: Serialize + Ord,
        V: Serial + DeserialWithState<S> + Deletable, {
        if self.ordered_set.remove(key) {
            self.map.remove(key);
        }
    }

    /// Get a reference to the value corresponding to the key.
    pub fn get(&self, key: &K) -> Option<StateRef<V>>
    where
        K: Serialize,
        S: HasStateApi,
        V: Serial + DeserialWithState<S>, {
        if self.ordered_set.is_empty() {
            None
        } else {
            self.map.get(key)
        }
    }

    /// Get a mutable reference to the value corresponding to the key.
    pub fn get_mut(&mut self, key: &K) -> Option<StateRefMut<V, S>>
    where
        K: Serialize,
        S: HasStateApi,
        V: Serial + DeserialWithState<S>, {
        if self.ordered_set.is_empty() {
            None
        } else {
            self.map.get_mut(key)
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    pub fn contains_key(&self, key: &K) -> bool
    where
        K: Serialize + Ord,
        S: HasStateApi, {
        self.ordered_set.contains(key)
    }

    /// Returns the smallest key in the map, which is strictly larger than the
    /// provided key. `None` meaning no such key is present in the map.
    pub fn higher(&self, key: &K) -> Option<StateRef<K>>
    where
        S: HasStateApi,
        K: Serialize + Ord, {
        self.ordered_set.higher(key)
    }

    /// Returns the largest key in the map, which is strictly smaller than the
    /// provided key. `None` meaning no such key is present in the map.
    pub fn lower(&self, key: &K) -> Option<StateRef<K>>
    where
        S: HasStateApi,
        K: Serialize + Ord, {
        self.ordered_set.lower(key)
    }

    /// Returns a reference to the first key in the map, if any. This key is
    /// always the minimum of all keys in the map.
    pub fn first_key(&self) -> Option<StateRef<K>>
    where
        S: HasStateApi,
        K: Serialize + Ord, {
        self.ordered_set.first()
    }

    /// Returns a reference to the last key in the map, if any. This key is
    /// always the maximum of all keys in the map.
    pub fn last_key(&self) -> Option<StateRef<K>>
    where
        S: HasStateApi,
        K: Serialize + Ord, {
        self.ordered_set.last()
    }

    /// Return the number of elements in the map.
    pub fn len(&self) -> u32 { self.ordered_set.len() }

    /// Returns `true` is the map contains no elements.
    pub fn is_empty(&self) -> bool { self.ordered_set.is_empty() }

    /// Create an iterator over the entries of [`StateBTreeMap`].
    /// Ordered by `K`.
    pub fn iter(&self) -> StateBTreeMapIter<K, V, S, M>
    where
        S: HasStateApi, {
        StateBTreeMapIter {
            key_iter: self.ordered_set.iter(),
            map:      &self.map,
        }
    }

    /// Clears the map, removing all key-value pairs.
    /// This also includes values pointed at, if `V`, for example, is a
    /// [StateBox]. **If applicable use [`clear_flat`](Self::clear_flat)
    /// instead.**
    pub fn clear(&mut self)
    where
        S: HasStateApi,
        K: Serialize,
        V: Serial + DeserialWithState<S> + Deletable, {
        self.map.clear();
        self.ordered_set.clear();
    }

    /// Clears the map, removing all key-value pairs.
    /// **This should be used over [`clear`](Self::clear) if it is
    /// applicable.** It avoids recursive deletion of values since the
    /// values are required to be _flat_.
    ///
    /// Unfortunately it is not possible to automatically choose between these
    /// implementations. Once Rust gets trait specialization then this might
    /// be possible.
    pub fn clear_flat(&mut self)
    where
        S: HasStateApi,
        K: Serialize,
        V: Serialize, {
        self.map.clear_flat();
        self.ordered_set.clear();
    }
}

/// An ordered set based on [B-Tree](https://en.wikipedia.org/wiki/B-tree), where
/// each node is stored separately in the low-level key-value store.
///
/// | Operation                                       | Performance   |
/// |-------------------------------------------------|---------------|
/// | [`contains`](Self::contains)                    | O(k + log(n)) |
/// | [`insert`](Self::insert)                        | O(k + log(n)) |
/// | [`remove`](Self::remove)                        | O(k + log(n)) |
/// | [`higher`](Self::higher)/[`lower`](Self::lower) | O(k + log(n)) |
///
/// Where `k` is the byte size of the serialized keys and `n` is the number of
/// entries in the map.
///
/// ## Type parameters
///
/// The map `StateBTreeSet<K, S, M>` is parametrized by the types:
/// - `K`: Keys used in the set. Most operations on the set require this to
///   implement [`Serialize`](crate::Serialize). Keys cannot contain references
///   to the low-level state, such as types containing [`StateBox`],
///   [`StateMap`] and [`StateSet`].
/// - `S`: The low-level state implementation used, this allows for mocking the
///   state API in unit tests, see
///   [`TestStateApi`](crate::test_infrastructure::TestStateApi).
/// - `M`: A `const usize` determining the _minimum degree_ of the B-tree.
///   _Must_ be a value of `2` or above for the tree to work. This can be used
///   to tweak the height of the tree vs size of each node in the tree. The
///   default is set based on benchmarks.
///
/// ## Usage
///
/// New sets can be constructed using the
/// [`new_btree_set`][StateBuilder::new_btree_set] method on the
/// [`StateBuilder`].
///
/// ```
/// # use concordium_std::*;
/// # use concordium_std::test_infrastructure::*;
/// # let mut state_builder = TestStateBuilder::new();
/// /// In an init method:
/// let mut map1 = state_builder.new_btree_set();
/// # map1.insert(0u8); // Specifies type of map.
///
/// # let mut host = TestHost::new((), state_builder);
/// /// In a receive method:
/// let mut map2 = host.state_builder().new_btree_set();
/// # map2.insert(0u16);
/// ```
///
/// ### **Caution**
///
/// `StateBTreeSet`s must be explicitly deleted when they are no longer needed,
/// otherwise they will remain in the contract's state, albeit unreachable.
///
/// ```no_run
/// # use concordium_std::*;
/// struct MyState<S: HasStateApi = StateApi> {
///     inner: StateBTreeSet<u64, S>,
/// }
/// fn incorrect_replace(state_builder: &mut StateBuilder, state: &mut MyState) {
///     // The following is incorrect. The old value of `inner` is not properly deleted.
///     // from the state.
///     state.inner = state_builder.new_btree_set(); // ⚠️
/// }
/// ```
/// Instead, the set should be [cleared](StateBTreeSet::clear):
///
/// ```no_run
/// # use concordium_std::*;
/// # struct MyState<S: HasStateApi = StateApi> {
/// #    inner: StateBTreeSet<u64, S>
/// # }
/// fn correct_replace(state_builder: &mut StateBuilder, state: &mut MyState) {
///     state.inner.clear();
/// }
/// ```
pub struct StateBTreeSet<K, S, const M: usize = 8> {
    /// Type marker for the key.
    _marker_key:  PhantomData<K>,
    /// The unique prefix to use for this map in the key-value store.
    prefix:       StateItemPrefix,
    /// The API for interacting with the low-level state.
    state_api:    S,
    /// The ID of the root node of the tree, where None represents the tree is
    /// empty.
    root:         Option<NodeId>,
    /// Tracking the number of items in the tree.
    len:          u32,
    /// Tracking the next available ID for a new node.
    next_node_id: NodeId,
}

impl<const M: usize, K, S> StateBTreeSet<K, S, M> {
    /// Construct a new [`StateBTreeSet`] given a unique prefix to use in the
    /// key-value store.
    pub(crate) fn new(state_api: S, prefix: StateItemPrefix) -> Self {
        Self {
            _marker_key: Default::default(),
            prefix,
            state_api,
            root: None,
            len: 0,
            next_node_id: NodeId {
                id: 0,
            },
        }
    }

    /// Insert a key into the set.
    /// Returns true if the key is new in the collection.
    pub fn insert(&mut self, key: K) -> bool
    where
        S: HasStateApi,
        K: Serialize + Ord, {
        let Some(root_id) = self.root else {
            let (node_id, _) = self.create_node(crate::vec![key], Vec::new());
            self.root = Some(node_id);
            self.len = 1;
            return true;
        };

        let root_node = self.get_node_mut(root_id);
        if !root_node.is_full() {
            let new = self.insert_non_full(root_node, key);
            if new {
                self.len += 1;
            }
            return new;
        } else if root_node.keys.binary_search(&key).is_ok() {
            return false;
        }
        // The root node is full, so we construct a new root node.
        let (new_root_id, mut new_root) = self.create_node(Vec::new(), crate::vec![root_id]);
        self.root = Some(new_root_id);
        // The old root node is now a child node.
        let mut child = root_node;
        let new_larger_child = self.split_child(&mut new_root, 0, &mut child);
        // new_root should now contain one key and two children, so we need to know
        // which one to insert into.
        let child = if new_root.keys[0] < key {
            new_larger_child
        } else {
            child
        };
        let new = self.insert_non_full(child, key);
        if new {
            self.len += 1;
        }
        new
    }

    /// Returns `true` if the set contains an element equal to the key.
    pub fn contains(&self, key: &K) -> bool
    where
        S: HasStateApi,
        K: Serialize + Ord, {
        let Some(root_node_id) = self.root else {
            return false;
        };
        let mut node = self.get_node(root_node_id);
        loop {
            let Err(child_index) = node.keys.binary_search(key) else {
                return true;
            };
            if node.is_leaf() {
                return false;
            }
            let child_node_id = node.children[child_index];
            node = self.get_node(child_node_id);
        }
    }

    /// Return the number of elements in the set.
    pub fn len(&self) -> u32 { self.len }

    /// Returns `true` is the set contains no elements.
    pub fn is_empty(&self) -> bool { self.root.is_none() }

    /// Get an iterator over the elements in the `StateBTreeSet`. The iterator
    /// returns elements in increasing order.
    pub fn iter(&self) -> StateBTreeSetIter<K, S, M>
    where
        S: HasStateApi, {
        StateBTreeSetIter {
            length:            self.len.try_into().unwrap_abort(),
            next_node:         self.root,
            depth_first_stack: Vec::new(),
            tree:              self,
            _marker_lifetime:  Default::default(),
        }
    }

    /// Clears the set, removing all elements.
    pub fn clear(&mut self)
    where
        S: HasStateApi, {
        // Reset the information.
        self.root = None;
        self.next_node_id = NodeId {
            id: 0,
        };
        self.len = 0;
        // Then delete every node store in the state.
        // Unwrapping is safe when only using the high-level API.
        self.state_api.delete_prefix(&self.prefix).unwrap_abort();
    }

    /// Returns the smallest key in the set, which is strictly larger than the
    /// provided key. `None` meaning no such key is present in the set.
    pub fn higher(&self, key: &K) -> Option<StateRef<K>>
    where
        S: HasStateApi,
        K: Serialize + Ord, {
        let Some(root_node_id) = self.root else {
            return None;
        };

        let mut node = self.get_node(root_node_id);
        let mut higher_so_far = None;
        loop {
            let higher_key_index = match node.keys.binary_search(key) {
                Ok(index) => index + 1,
                Err(index) => index,
            };

            if node.is_leaf() {
                return if higher_key_index < node.keys.len() {
                    // This does not mutate the node in the end, just the representation in memory
                    // which is freed after the call.
                    Some(StateRef::new(node.keys.swap_remove(higher_key_index)))
                } else {
                    higher_so_far
                };
            } else {
                if higher_key_index < node.keys.len() {
                    // This does not mutate the node in the end, just the representation in memory
                    // which is freed after the call.
                    higher_so_far = Some(StateRef::new(node.keys.swap_remove(higher_key_index)))
                }

                let child_node_id = node.children[higher_key_index];
                node = self.get_node(child_node_id);
            }
        }
    }

    /// Returns the largest key in the set, which is strictly smaller than the
    /// provided key. `None` meaning no such key is present in the set.
    pub fn lower(&self, key: &K) -> Option<StateRef<K>>
    where
        S: HasStateApi,
        K: Serialize + Ord, {
        let Some(root_node_id) = self.root else {
            return None;
        };

        let mut node = self.get_node(root_node_id);
        let mut lower_so_far = None;
        loop {
            let lower_key_index = match node.keys.binary_search(key) {
                Ok(index) => index,
                Err(index) => index,
            };

            if node.is_leaf() {
                return if lower_key_index == 0 {
                    lower_so_far
                } else {
                    // lower_key_index cannot be 0 in this case, since the binary search will only
                    // return 0 in the true branch above.
                    Some(StateRef::new(node.keys.swap_remove(lower_key_index - 1)))
                };
            } else {
                if lower_key_index > 0 {
                    // This does not mutate the node in the end, just the representation in memory
                    // which is freed after the call.
                    lower_so_far = Some(StateRef::new(node.keys.swap_remove(lower_key_index - 1)));
                }
                let child_node_id = node.children[lower_key_index];
                node = self.get_node(child_node_id)
            }
        }
    }

    /// Returns a reference to the first key in the set, if any. This key is
    /// always the minimum of all keys in the set.
    pub fn first(&self) -> Option<StateRef<K>>
    where
        S: HasStateApi,
        K: Serialize + Ord, {
        let Some(root_node_id) = self.root else {
            return None;
        };
        let mut root = self.get_node(root_node_id);
        if root.is_leaf() {
            Some(StateRef::new(root.keys.swap_remove(0)))
        } else {
            Some(StateRef::new(self.get_lowest_key(&root, 0)))
        }
    }

    /// Returns a reference to the last key in the set, if any. This key is
    /// always the maximum of all keys in the set.
    pub fn last(&self) -> Option<StateRef<K>>
    where
        S: HasStateApi,
        K: Serialize + Ord, {
        let Some(root_node_id) = self.root else {
            return None;
        };
        let mut root = self.get_node(root_node_id);
        if root.is_leaf() {
            Some(StateRef::new(root.keys.pop().unwrap_abort()))
        } else {
            Some(StateRef::new(self.get_highest_key(&root, root.children.len() - 1)))
        }
    }

    /// Remove a key from the set.
    /// Returns whether such an element was present.
    pub fn remove(&mut self, key: &K) -> bool
    where
        K: Ord + Serialize,
        S: HasStateApi, {
        let Some(root_node_id) = self.root else {
            return false;
        };

        let deleted_something = {
            let mut node = self.get_node_mut(root_node_id);
            loop {
                match node.keys.binary_search(key) {
                    Ok(index) => {
                        if node.is_leaf() {
                            // Found the key in this node and the node is a leaf, meaning we
                            // simply remove it.
                            // This will not violate the minimum keys invariant, since a node
                            // ensures a child can spare a key before iteration and the root
                            // node is not part of the
                            // invariant.
                            node.keys.remove(index);
                            break true;
                        }
                        // Found the key in this node, but the node is not a leaf.
                        let mut left_child = self.get_node_mut(node.children[index]);
                        if !left_child.is_at_min() {
                            // If the child with smaller keys can spare a key, we take the
                            // highest key from it.
                            node.keys[index] = self.remove_largest_key(left_child);
                            break true;
                        }

                        let right_child = self.get_node_mut(node.children[index + 1]);
                        if !right_child.is_at_min() {
                            // If the child with larger keys can spare a key, we take the lowest
                            // key from it.
                            node.keys[index] = self.remove_smallest_key(right_child);
                            break true;
                        }
                        // No child on either side of the key can spare a key at this point, so
                        // we merge them into one child, moving the
                        // key into the merged child and try
                        // to remove from this.
                        self.merge(&mut node, index, &mut left_child, right_child);
                        node = left_child;
                        continue;
                    }
                    Err(index) => {
                        // Node did not contain the key.
                        if node.is_leaf() {
                            break false;
                        }
                        // Node did not contain the key and is not a leaf.
                        // Check and proactively prepare the child to be able to delete a key.
                        node = self.prepare_child_for_key_removal(node, index);
                    }
                };
            }
        };

        // If something was deleted, we update the length and make sure to remove the
        // root node if needed.
        let root = self.get_node_mut(root_node_id);
        if deleted_something {
            self.len -= 1;
            if self.len == 0 {
                // Remote the root node if tree is empty.
                self.root = None;
                self.delete_node(root);
                return true;
            }
        }
        // If the root is empty but the tree is not, point to the only child of the root
        // as the root.
        if root.keys.is_empty() {
            self.root = Some(root.children[0]);
            self.delete_node(root);
        }
        deleted_something
    }

    /// Internal function for taking the largest key in a subtree.
    ///
    /// Assumes:
    /// - The provided node is not the root.
    /// - The node contain more than minimum number of keys.
    fn remove_largest_key(&mut self, mut node: StateRefMut<'_, Node<M, K>, S>) -> K
    where
        K: Ord + Serialize,
        S: HasStateApi, {
        while !node.is_leaf() {
            // Node is not a leaf, so we move further down this subtree.
            let child_index = node.children.len() - 1;
            node = self.prepare_child_for_key_removal(node, child_index);
        }
        // The node is a leaf, meaning we simply remove it.
        // This will not violate the minimum keys invariant, since a node
        // ensures a child can spare a key before iteration.
        node.keys.pop().unwrap_abort()
    }

    /// Internal function for taking the smallest key in a subtree.
    ///
    /// Assumes:
    /// - The provided node is not the root.
    /// - The provided `node` contain more than minimum number of keys.
    fn remove_smallest_key(&mut self, mut node: StateRefMut<'_, Node<M, K>, S>) -> K
    where
        K: Ord + Serialize,
        S: HasStateApi, {
        while !node.is_leaf() {
            // Node is not a leaf, so we move further down this subtree.
            let child_index = 0;
            node = self.prepare_child_for_key_removal(node, child_index);
        }
        // The node is a leaf, meaning we simply remove it.
        // This will not violate the minimum keys invariant, since a node
        // ensures a child can spare a key before iteration.
        node.keys.remove(0)
    }

    /// Internal function for key rotation, preparing a node for deleting a key.
    /// Returns the now prepared child at `index`.
    /// Assumes:
    /// - The provided `node` is not a leaf and has a child at `index`.
    /// - The minimum degree `M` is at least 2 or more.
    fn prepare_child_for_key_removal<'b, 'c>(
        &mut self,
        mut node: StateRefMut<'b, Node<M, K>, S>,
        index: usize,
    ) -> StateRefMut<'c, Node<M, K>, S>
    where
        K: Ord + Serialize,
        S: HasStateApi, {
        let mut child = self.get_node_mut(node.children[index]);
        if !child.is_at_min() {
            return child;
        }
        // The child is at minimum keys, so first attempt to take a key from either
        // sibling, otherwise merge with one of them.
        let has_smaller_sibling = 0 < index;
        let has_larger_sibling = index < node.children.len() - 1;
        let smaller_sibling = if has_smaller_sibling {
            let mut smaller_sibling = self.get_node_mut(node.children[index - 1]);
            if !smaller_sibling.is_at_min() {
                // The smaller sibling can spare a key, so we replace the largest
                // key from the sibling, put it in
                // the parent and take a key from
                // the parent.
                let largest_key_sibling = smaller_sibling.keys.pop().unwrap_abort();
                let swapped_node_key = mem::replace(&mut node.keys[index - 1], largest_key_sibling);
                child.keys.insert(0, swapped_node_key);
                if !child.is_leaf() {
                    child.children.insert(0, smaller_sibling.children.pop().unwrap_abort());
                }
                return child;
            }
            Some(smaller_sibling)
        } else {
            None
        };
        let larger_sibling = if has_larger_sibling {
            let mut larger_sibling = self.get_node_mut(node.children[index + 1]);
            if !larger_sibling.is_at_min() {
                // The larger sibling can spare a key, so we replace the smallest
                // key from the sibling, put it in
                // the parent and take a key from
                // the parent.
                let first_key_sibling = larger_sibling.keys.remove(0);
                let swapped_node_key = mem::replace(&mut node.keys[index], first_key_sibling);
                child.keys.push(swapped_node_key);

                if !child.is_leaf() {
                    child.children.push(larger_sibling.children.remove(0));
                }
                return child;
            }
            Some(larger_sibling)
        } else {
            None
        };

        if let Some(sibling) = larger_sibling {
            self.merge(&mut node, index, &mut child, sibling);
            child
        } else if let Some(mut sibling) = smaller_sibling {
            self.merge(&mut node, index - 1, &mut sibling, child);
            sibling
        } else {
            // Unreachable code, since M must be 2 or larger (the minimum degree), a
            // child node must have at least one sibling.
            crate::trap();
        }
    }

    /// Internal function for getting the highest key in a subtree.
    /// Assumes the provided `node` is not a leaf and has a child at
    /// `child_index`.
    fn get_highest_key(&self, node: &Node<M, K>, child_index: usize) -> K
    where
        K: Ord + Serialize,
        S: HasStateApi, {
        let mut node = self.get_node(node.children[child_index]);
        while !node.is_leaf() {
            let child_node_id = node.children.last().unwrap_abort();
            node = self.get_node(*child_node_id);
        }
        // This does not mutate the node in the end, just the representation in memory
        // which is freed after the call.
        node.keys.pop().unwrap_abort()
    }

    /// Internal function for getting the lowest key in a subtree.
    /// Assumes the provided `node` is not a leaf and has a child at
    /// `child_index`.
    fn get_lowest_key(&self, node: &Node<M, K>, child_index: usize) -> K
    where
        K: Ord + Serialize,
        S: HasStateApi, {
        let mut node = self.get_node(node.children[child_index]);
        while !node.is_leaf() {
            let child_node_id = node.children.first().unwrap_abort();
            node = self.get_node(*child_node_id);
        }
        // This does not mutate the node in the end, just the representation in memory
        // which is freed after the call.
        node.keys.swap_remove(0)
    }

    /// Moving key at `index` from the node to the lower child and then merges
    /// this child with the content of its larger sibling, deleting the sibling.
    ///
    /// Assumes:
    /// - `parent_node` has children `child` at `index` and `larger_child` at
    ///   `index + 1`.
    /// - Both children are at minimum number of keys (`M - 1`).
    fn merge(
        &mut self,
        parent_node: &mut Node<M, K>,
        index: usize,
        child: &mut Node<M, K>,
        mut larger_child: StateRefMut<Node<M, K>, S>,
    ) where
        K: Ord + Serialize,
        S: HasStateApi, {
        let parent_key = parent_node.keys.remove(index);
        parent_node.children.remove(index + 1);
        child.keys.push(parent_key);
        child.keys.append(&mut larger_child.keys);
        child.children.append(&mut larger_child.children);
        self.delete_node(larger_child);
    }

    /// Internal function for constructing a node. It will increment the next
    /// node ID and create an entry in the smart contract key-value store.
    fn create_node<'b>(
        &mut self,
        keys: Vec<K>,
        children: Vec<NodeId>,
    ) -> (NodeId, StateRefMut<'b, Node<M, K>, S>)
    where
        K: Serialize,
        S: HasStateApi, {
        let node_id = self.next_node_id.copy_then_increment();
        let node = Node {
            keys,
            children,
        };
        let entry = self.state_api.create_entry(&node_id.as_key(&self.prefix)).unwrap_abort();
        let mut ref_mut: StateRefMut<'_, Node<M, K>, S> =
            StateRefMut::new(entry, self.state_api.clone());
        ref_mut.set(node);
        (node_id, ref_mut)
    }

    /// Internal function for deleting a node, removing the entry in the smart
    /// contract key-value store. Traps if no node was present.
    fn delete_node(&mut self, node: StateRefMut<Node<M, K>, S>)
    where
        K: Serial,
        S: HasStateApi, {
        self.state_api.delete_entry(node.into_raw_parts().1).unwrap_abort()
    }

    /// Internal function for inserting into a subtree.
    /// Assumes the given node is not full.
    fn insert_non_full(&mut self, initial_node: StateRefMut<Node<M, K>, S>, key: K) -> bool
    where
        K: Serialize + Ord,
        S: HasStateApi, {
        let mut node = initial_node;
        loop {
            let Err(insert_index) = node.keys.binary_search(&key) else {
                // We find the key in this node, so we do nothing.
                return false;
            };
            // The key is not in this node.
            if node.is_leaf() {
                // Since we can assume the node is not full and this is a leaf, we can just
                // insert here.
                node.keys.insert(insert_index, key);
                return true;
            }

            // The node is not a leaf, so we want to insert in the relevant child node.
            let mut child = self.get_node_mut(node.children[insert_index]);
            node = if !child.is_full() {
                child
            } else {
                let larger_child = self.split_child(&mut node, insert_index, &mut child);
                // Since the child is now split into two, we have to check which one to insert
                // into.
                let moved_up_key = &node.keys[insert_index];
                if moved_up_key == &key {
                    // If the key moved up during the split is the key we are inserting, we exit.
                    return false;
                } else if moved_up_key < &key {
                    larger_child
                } else {
                    child
                }
            };
        }
    }

    /// Internal function for splitting the child node at a given index for a
    /// given node. This will also mutate the given node adding a new key
    /// and child after the provided child_index.
    /// Returns the newly created node.
    ///
    /// Assumes:
    /// - Node is not a leaf and has `child` as child at `child_index`.
    /// - `child` is at maximum keys (`2 * M - 1`).
    fn split_child<'b>(
        &mut self,
        node: &mut Node<M, K>,
        child_index: usize,
        child: &mut Node<M, K>,
    ) -> StateRefMut<'b, Node<M, K>, S>
    where
        K: Serialize + Ord,
        S: HasStateApi, {
        let split_index = Node::<M, K>::MINIMUM_KEY_LEN + 1;
        let (new_larger_sibling_id, new_larger_sibling) = self.create_node(
            child.keys.split_off(split_index),
            if child.is_leaf() {
                Vec::new()
            } else {
                child.children.split_off(split_index)
            },
        );
        let key = child.keys.pop().unwrap_abort();
        node.children.insert(child_index + 1, new_larger_sibling_id);
        node.keys.insert(child_index, key);
        new_larger_sibling
    }

    /// Internal function for looking up a node in the tree.
    /// This assumes the node is present and traps if this is not the case.
    fn get_node<Key>(&self, node_id: NodeId) -> Node<M, Key>
    where
        Key: Deserial,
        S: HasStateApi, {
        let key = node_id.as_key(&self.prefix);
        let mut entry = self.state_api.lookup_entry(&key).unwrap_abort();
        entry.get().unwrap_abort()
    }

    /// Internal function for looking up a node, providing mutable access.
    /// This assumes the node is present and traps if this is not the case.
    fn get_node_mut<'b>(&mut self, node_id: NodeId) -> StateRefMut<'b, Node<M, K>, S>
    where
        K: Serial,
        S: HasStateApi, {
        let key = node_id.as_key(&self.prefix);
        let entry = self.state_api.lookup_entry(&key).unwrap_abort();
        StateRefMut::new(entry, self.state_api.clone())
    }

    /// Construct a string for displaying the btree and debug information.
    /// Should only be used while debugging and testing the btree itself.
    #[cfg(all(feature = "wasm-test", feature = "concordium-quickcheck"))]
    pub(crate) fn debug(&self) -> String
    where
        K: Serialize + std::fmt::Debug + Ord,
        S: HasStateApi, {
        let Some(root_node_id) = self.root else {
            return format!("no root");
        };
        let mut string = String::new();
        let root: Node<M, K> = self.get_node(root_node_id);
        string.push_str(format!("root: {:#?}", root).as_str());
        let mut stack = root.children;

        while let Some(node_id) = stack.pop() {
            let node: Node<M, K> = self.get_node(node_id);
            string.push_str(
                format!("node {} {:?}: {:#?},\n", node_id.id, node.check_invariants(), node)
                    .as_str(),
            );

            stack.extend(node.children);
        }
        string
    }

    /// Check a number of invariants, producing an error if any of them are
    /// violated. Should only be used while debugging and testing the btree
    /// itself.
    #[cfg(all(feature = "wasm-test", feature = "concordium-quickcheck"))]
    pub(crate) fn check_invariants(&self) -> Result<(), InvariantViolation>
    where
        K: Serialize + Ord,
        S: HasStateApi, {
        use crate::ops::Deref;
        let Some(root_node_id) = self.root else {
            return if self.len == 0 {
                Ok(())
            } else {
                Err(InvariantViolation::NonZeroLenWithNoRoot)
            };
        };
        let root: Node<M, K> = self.get_node(root_node_id);
        if root.keys.is_empty() {
            return Err(InvariantViolation::ZeroKeysInRoot);
        }

        let mut stack = root.children;
        while let Some(node_id) = stack.pop() {
            let node: Node<M, K> = self.get_node(node_id);
            node.check_invariants()?;
            stack.extend(node.children);
        }

        let mut prev = None;
        for key in self.iter() {
            if let Some(p) = prev.as_deref() {
                if p >= key.deref() {
                    return Err(InvariantViolation::IterationOutOfOrder);
                }
            }
            prev = Some(key);
        }
        Ok(())
    }
}

/// An iterator over the entries of a [`StateBTreeSet`].
///
/// Ordered by `K`.
///
/// This `struct` is created by the [`iter`][StateBTreeSet::iter] method on
/// [`StateBTreeSet`]. See its documentation for more.
pub struct StateBTreeSetIter<'a, 'b, K, S, const M: usize> {
    /// The number of elements left to iterate.
    length:            usize,
    /// Reference to a node in the tree to load and iterate before the current
    /// node.
    next_node:         Option<NodeId>,
    /// Tracking the nodes depth first, which are currently being iterated.
    depth_first_stack: Vec<(Node<M, KeyWrapper<K>>, usize)>,
    /// Reference to the set, needed for looking up the nodes.
    tree:              &'a StateBTreeSet<K, S, M>,
    /// Marker for tracking the lifetime of the key.
    _marker_lifetime:  PhantomData<&'b K>,
}

impl<'a, 'b, const M: usize, K, S> Iterator for StateBTreeSetIter<'a, 'b, K, S, M>
where
    'a: 'b,
    K: Deserial,
    S: HasStateApi,
{
    type Item = StateRef<'b, K>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(id) = self.next_node.take() {
            let node = self.tree.get_node(id);
            if !node.is_leaf() {
                self.next_node = Some(node.children[0]);
            }
            self.depth_first_stack.push((node, 0));
        }

        if let Some((node, index)) = self.depth_first_stack.last_mut() {
            let key = node.keys[*index].key.take().unwrap_abort();
            *index += 1;
            let no_more_keys = index == &node.keys.len();
            if !node.is_leaf() {
                let child_id = node.children[*index];
                self.next_node = Some(child_id);
            }
            if no_more_keys {
                self.depth_first_stack.pop();
            }
            self.length -= 1;
            Some(StateRef::new(key))
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) { (self.length, Some(self.length)) }
}

/// An iterator over the entries of a [`StateBTreeMap`].
///
/// Ordered by `K`.
///
/// This `struct` is created by the [`iter`][StateBTreeMap::iter] method on
/// [`StateBTreeMap`]. See its documentation for more.
pub struct StateBTreeMapIter<'a, 'b, K, V, S, const M: usize> {
    /// Iterator over the keys in the map.
    key_iter: StateBTreeSetIter<'a, 'b, K, S, M>,
    /// Reference to the map holding the values.
    map:      &'a StateMap<K, V, S>,
}

impl<'a, 'b, const M: usize, K, V, S> Iterator for StateBTreeMapIter<'a, 'b, K, V, S, M>
where
    'a: 'b,
    K: Serialize,
    V: Serial + DeserialWithState<S> + 'b,
    S: HasStateApi,
{
    type Item = (StateRef<'b, K>, StateRef<'b, V>);

    fn next(&mut self) -> Option<Self::Item> {
        let next_key = self.key_iter.next()?;
        let value = self.map.get(&next_key).unwrap_abort();
        // Unwrap is safe, otherwise the map and the set have inconsistencies.
        Some((next_key, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) { self.key_iter.size_hint() }
}

/// Identifier for a node in the tree. Used to construct the key, where this
/// node is store in the smart contract key-value store.
#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
struct NodeId {
    id: u32,
}

/// Byte size of the key used to store a BTree internal node in the smart
/// contract key-value store.
const BTREE_NODE_KEY_SIZE: usize = STATE_ITEM_PREFIX_SIZE + NodeId::SERIALIZED_BYTE_SIZE;

impl NodeId {
    /// Byte size of `NodeId` when serialized.
    const SERIALIZED_BYTE_SIZE: usize = 4;

    /// Return a copy of the NodeId, then increments itself.
    fn copy_then_increment(&mut self) -> Self {
        let current = *self;
        self.id += 1;
        current
    }

    /// Construct the key for the node in the key-value store from the node ID.
    fn as_key(&self, prefix: &StateItemPrefix) -> [u8; BTREE_NODE_KEY_SIZE] {
        // Create an uninitialized array of `MaybeUninit`. The `assume_init` is
        // safe because the type we are claiming to have initialized here is a
        // bunch of `MaybeUninit`s, which do not require initialization.
        let mut prefixed: [mem::MaybeUninit<u8>; BTREE_NODE_KEY_SIZE] =
            unsafe { mem::MaybeUninit::uninit().assume_init() };
        for i in 0..STATE_ITEM_PREFIX_SIZE {
            prefixed[i].write(prefix[i]);
        }
        let id_bytes = self.id.to_le_bytes();
        for i in 0..id_bytes.len() {
            prefixed[STATE_ITEM_PREFIX_SIZE + i].write(id_bytes[i]);
        }
        // Transmuting away the maybeuninit is safe since we have initialized all of
        // them.
        unsafe { mem::transmute(prefixed) }
    }
}

/// Type representing a node in the [`StateBTreeMap`].
/// Each node is stored separately in the smart contract key-value store.
#[derive(Debug)]
struct Node<const M: usize, K> {
    /// List of sorted keys tracked by this node.
    /// This list should never be empty and contain between `M - 1` and `2M
    /// - 1` elements. The root node being the only exception to this.
    keys:     Vec<K>,
    /// List of nodes which are children of this node in the tree.
    ///
    /// This list is empty when this node is representing a leaf.
    /// When not a leaf, it will contain exactly `keys.len() + 1` elements.
    ///
    /// The elements are ordered such that for a key `keys[i]`:
    /// - `children[i]` is a subtree containing strictly smaller keys.
    /// - `children[i + 1]` is a subtree containing strictly larger keys.
    children: Vec<NodeId>,
}

impl<const M: usize, K> Node<M, K> {
    /// The max length of the child list.
    const MAXIMUM_CHILD_LEN: usize = 2 * M;
    /// The max length of the key list.
    const MAXIMUM_KEY_LEN: usize = Self::MAXIMUM_CHILD_LEN - 1;
    /// The min length of the child list, when the node is not a leaf node.
    const MINIMUM_CHILD_LEN: usize = M;
    /// The min length of the key list, except when the node is root.
    const MINIMUM_KEY_LEN: usize = Self::MINIMUM_CHILD_LEN - 1;

    /// The number of keys stored in this node.
    fn len(&self) -> usize { self.keys.len() }

    /// Check if the node holds the maximum number of keys.
    fn is_full(&self) -> bool { self.len() == Self::MAXIMUM_KEY_LEN }

    /// Check if the node is representing a leaf in the tree.
    fn is_leaf(&self) -> bool { self.children.is_empty() }

    /// Check if the node holds the minimum number of keys.
    fn is_at_min(&self) -> bool { self.len() == Self::MINIMUM_KEY_LEN }

    /// Check a number of invariants of a non-root node in a btree, producing an
    /// error if any of them are violated. Should only be used while
    /// debugging and testing the btree itself.
    #[cfg(all(feature = "wasm-test", feature = "concordium-quickcheck"))]
    pub(crate) fn check_invariants(&self) -> Result<(), InvariantViolation>
    where
        K: Ord, {
        for i in 1..self.keys.len() {
            if &self.keys[i - 1] >= &self.keys[i] {
                return Err(InvariantViolation::NodeKeysOutOfOrder);
            }
        }

        if self.keys.len() < Self::MINIMUM_KEY_LEN {
            return Err(InvariantViolation::KeysLenBelowMin);
        }
        if self.keys.len() > Self::MAXIMUM_KEY_LEN {
            return Err(InvariantViolation::KeysLenAboveMax);
        }

        if self.is_leaf() {
            if !self.children.is_empty() {
                return Err(InvariantViolation::LeafWithChildren);
            }
        } else {
            if self.children.len() < Self::MINIMUM_CHILD_LEN {
                return Err(InvariantViolation::ChildrenLenBelowMin);
            }
            if self.children.len() > Self::MAXIMUM_CHILD_LEN {
                return Err(InvariantViolation::ChildrenLenAboveMax);
            }
        }

        Ok(())
    }
}

/// The invariants to check in a btree.
/// Should only be used while debugging and testing the btree itself.
#[cfg(all(feature = "wasm-test", feature = "concordium-quickcheck"))]
#[derive(Debug)]
pub(crate) enum InvariantViolation {
    NonZeroLenWithNoRoot,
    ZeroKeysInRoot,
    IterationOutOfOrder,
    NodeKeysOutOfOrder,
    KeysLenBelowMin,
    KeysLenAboveMax,
    LeafWithChildren,
    ChildrenLenBelowMin,
    ChildrenLenAboveMax,
}

/// Wrapper implement the exact same deserial as K, but wraps it in an
/// option in memory. This is used, to allow taking a key from a mutable
/// reference to a node, without cloning the key, during iteration of the
/// set.
#[repr(transparent)]
struct KeyWrapper<K> {
    key: Option<K>,
}

impl<K: Deserial> Deserial for KeyWrapper<K> {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let key = K::deserial(source)?;
        Ok(Self {
            key: Some(key),
        })
    }
}

impl<const M: usize, K, V, S> Serial for StateBTreeMap<K, V, S, M> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.map.serial(out)?;
        self.ordered_set.serial(out)
    }
}

impl<const M: usize, K, V, S: HasStateApi> DeserialWithState<S> for StateBTreeMap<K, V, S, M> {
    fn deserial_with_state<R: Read>(state: &S, source: &mut R) -> ParseResult<Self> {
        let map = DeserialWithState::deserial_with_state(state, source)?;
        let ordered_set = DeserialWithState::deserial_with_state(state, source)?;
        Ok(Self {
            map,
            ordered_set,
        })
    }
}

impl<const M: usize, K, S> Serial for StateBTreeSet<K, S, M> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.prefix.serial(out)?;
        self.root.serial(out)?;
        self.len.serial(out)?;
        self.next_node_id.serial(out)
    }
}

impl<const M: usize, K, S: HasStateApi> DeserialWithState<S> for StateBTreeSet<K, S, M> {
    fn deserial_with_state<R: Read>(state: &S, source: &mut R) -> ParseResult<Self> {
        let prefix = source.get()?;
        let root = source.get()?;
        let len = source.get()?;
        let next_node_id = source.get()?;

        Ok(Self {
            _marker_key: Default::default(),
            prefix,
            state_api: state.clone(),
            root,
            len,
            next_node_id,
        })
    }
}

impl<const M: usize, K: Serial> Serial for Node<M, K> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.keys.serial(out)?;
        self.children.serial(out)
    }
}

impl<const M: usize, K: Deserial> Deserial for Node<M, K> {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        let keys = source.get()?;
        let children = source.get()?;
        Ok(Self {
            keys,
            children,
        })
    }
}

impl Serial for NodeId {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> { self.id.serial(out) }
}

impl Deserial for NodeId {
    fn deserial<R: Read>(source: &mut R) -> ParseResult<Self> {
        Ok(Self {
            id: source.get()?,
        })
    }
}

impl<const M: usize, K, V, S> Deletable for StateBTreeMap<K, V, S, M>
where
    S: HasStateApi,
    K: Serialize,
    V: Serial + DeserialWithState<S> + Deletable,
{
    fn delete(mut self) { self.clear(); }
}

/// This test module rely on the runtime providing host functions and can only
/// be run using `cargo concordium test`.
#[cfg(feature = "wasm-test")]
mod wasm_test_btree {
    use crate::{claim, claim_eq, concordium_test, StateApi, StateBuilder};

    #[concordium_test]
    fn test_btree_insert_6() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<5, _>();
        for n in 0..=5 {
            tree.insert(n);
        }
        for n in 0..=5 {
            claim!(tree.contains(&n));
        }
    }

    #[concordium_test]
    fn test_btree_insert_0_7() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..=7 {
            tree.insert(n);
        }
        for n in 0..=7 {
            claim!(tree.contains(&n));
        }
    }

    #[concordium_test]
    fn test_btree_insert_7_no_order() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();

        tree.insert(0);
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree.insert(7);
        tree.insert(6);
        tree.insert(5);
        tree.insert(4);

        for n in 0..=7 {
            claim!(tree.contains(&n));
        }
    }

    #[concordium_test]
    fn test_btree_higher() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree.insert(4);
        tree.insert(5);
        tree.insert(7);
        claim_eq!(tree.higher(&3).as_deref(), Some(&4));
        claim_eq!(tree.higher(&5).as_deref(), Some(&7));
        claim_eq!(tree.higher(&6).as_deref(), Some(&7));
        claim_eq!(tree.higher(&7).as_deref(), None)
    }

    #[concordium_test]
    fn test_btree_lower() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree.insert(4);
        tree.insert(5);
        tree.insert(7);
        claim_eq!(tree.lower(&3).as_deref(), Some(&2));
        claim_eq!(tree.lower(&7).as_deref(), Some(&5));
        claim_eq!(tree.lower(&6).as_deref(), Some(&5));
        claim_eq!(tree.lower(&1).as_deref(), None)
    }

    #[concordium_test]
    fn test_btree_insert_1000() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..500 {
            tree.insert(n);
        }

        for n in (500..1000).into_iter().rev() {
            tree.insert(n);
        }

        for n in 0..1000 {
            claim!(tree.contains(&n))
        }

        claim_eq!(tree.len(), 1000)
    }

    #[concordium_test]
    fn test_btree_7_get_8() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..=7 {
            tree.insert(n);
        }

        claim!(!tree.contains(&8));
    }

    #[concordium_test]
    fn test_btree_remove_from_one_node_tree() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..3 {
            tree.insert(n);
        }
        claim!(tree.contains(&1));
        claim!(tree.remove(&1));
        claim!(tree.contains(&0));
        claim!(!tree.contains(&1));
        claim!(tree.contains(&2));
    }

    #[concordium_test]
    fn test_btree_remove_only_key_lower_leaf_in_three_node() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..4 {
            tree.insert(n);
        }
        tree.remove(&3);

        claim!(tree.contains(&0));
        claim!(tree.remove(&0));
        claim!(!tree.contains(&0));
        claim!(tree.contains(&1));
        claim!(tree.contains(&2));
    }

    #[concordium_test]
    fn test_btree_remove_only_key_higher_leaf_in_three_node() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in (0..4).into_iter().rev() {
            tree.insert(n);
        }
        tree.remove(&3);
        claim!(tree.contains(&2));
        claim!(tree.remove(&2));
        claim!(tree.contains(&0));
        claim!(tree.contains(&1));
        claim!(!tree.contains(&2));
    }

    #[concordium_test]
    fn test_btree_remove_from_higher_leaf_in_three_node_taking_from_sibling() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in (0..4).into_iter().rev() {
            tree.insert(n);
        }
        claim!(tree.contains(&3));
        claim!(tree.remove(&3));
        claim!(!tree.contains(&3));
    }

    #[concordium_test]
    fn test_btree_remove_from_lower_leaf_in_three_node_taking_from_sibling() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..4 {
            tree.insert(n);
        }
        claim!(tree.contains(&0));
        claim!(tree.remove(&0));
        claim!(!tree.contains(&0));
        claim!(tree.contains(&1));
        claim!(tree.contains(&2));
        claim!(tree.contains(&3));
    }

    #[concordium_test]
    fn test_btree_remove_from_root_in_three_node_causing_merge() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..4 {
            tree.insert(n);
        }
        tree.remove(&3);

        claim!(tree.contains(&1));
        claim!(tree.remove(&1));
        claim!(!tree.contains(&1));
    }

    #[concordium_test]
    fn test_btree_remove_from_root_in_three_node_taking_key_from_higher_child() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..4 {
            tree.insert(n);
        }
        claim!(tree.contains(&1));
        claim!(tree.remove(&1));
        claim!(!tree.contains(&1));
    }

    #[concordium_test]
    fn test_btree_remove_from_root_in_three_node_taking_key_from_lower_child() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in (0..4).into_iter().rev() {
            tree.insert(n);
        }
        claim!(tree.contains(&2));
        claim!(tree.remove(&2));
        claim!(!tree.contains(&2));
    }

    #[concordium_test]
    fn test_btree_iter() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        let keys: Vec<u32> = (0..15).into_iter().collect();
        for &k in &keys {
            tree.insert(k);
        }
        let iter_keys: Vec<u32> = tree.iter().map(|k| k.clone()).collect();
        claim_eq!(keys, iter_keys);
    }

    #[concordium_test]
    fn test_btree_insert_present_key() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in [0, 3, 4, 1, 2].into_iter() {
            tree.insert(n);
        }
        claim!(!tree.insert(1));
    }

    #[cfg(feature = "concordium-quickcheck")]
    #[allow(deprecated)]
    mod quickcheck {
        use super::super::*;
        use crate::{
            self as concordium_std, concordium_quickcheck, concordium_test, fail, StateApi,
            StateBuilder,
        };
        use ::quickcheck::{Arbitrary, Gen, TestResult};

        #[concordium_quickcheck]
        fn test_quickcheck_inserts(items: Vec<u32>) -> TestResult {
            let mut state_builder = StateBuilder::open(StateApi::open());
            let mut tree = state_builder.new_btree_set_degree::<2, _>();
            for k in items.clone() {
                tree.insert(k);
            }
            if let Err(violation) = tree.check_invariants() {
                return TestResult::error(format!("Invariant violated: {:?}", violation));
            }
            for k in items.iter() {
                if !tree.contains(k) {
                    return TestResult::error(format!("Missing key: {}", k));
                }
            }
            TestResult::passed()
        }

        #[concordium_quickcheck(num_tests = 500)]
        fn test_quickcheck_inserts_removes(mutations: Mutations<u32>) -> TestResult {
            let mut state_builder = StateBuilder::open(StateApi::open());
            let mut tree = state_builder.new_btree_set_degree::<2, _>();

            if let Err(err) = run_mutations(&mut tree, &mutations.0) {
                TestResult::error(format!("Error: {}, tree: {}", err, tree.debug()))
            } else {
                TestResult::passed()
            }
        }

        #[derive(Debug, Clone)]
        struct Mutations<K>(Vec<(K, Operation)>);

        #[derive(Debug, Clone, Copy)]
        enum Operation {
            InsertKeyNotPresent,
            InsertKeyPresent,
            RemoveKeyPresent,
            RemoveKeyNotPresent,
        }

        fn run_mutations<const M: usize, S: HasStateApi>(
            tree: &mut StateBTreeSet<u32, S, M>,
            mutations: &[(u32, Operation)],
        ) -> Result<(), String> {
            for (k, op) in mutations.into_iter() {
                if let Err(violation) = tree.check_invariants() {
                    return Err(format!("Invariant violated: {:?}", violation));
                }
                match op {
                    Operation::InsertKeyPresent => {
                        if tree.insert(*k) {
                            return Err(format!("InsertKeyPresent was not present: {}", k));
                        }
                    }
                    Operation::InsertKeyNotPresent => {
                        if !tree.insert(*k) {
                            return Err(format!("InsertKeyNotPresent was present: {}", k));
                        }
                    }
                    Operation::RemoveKeyNotPresent => {
                        if tree.remove(k) {
                            return Err(format!("RemoveKeyNotPresent was present: {}", k));
                        }
                    }
                    Operation::RemoveKeyPresent => {
                        if !tree.remove(k) {
                            return Err(format!("RemoveKeyPresent was not present: {}", k));
                        }
                    }
                }
            }
            Ok(())
        }

        impl Arbitrary for Operation {
            fn arbitrary(g: &mut Gen) -> Self {
                g.choose(&[
                    Self::InsertKeyNotPresent,
                    Self::InsertKeyPresent,
                    Self::RemoveKeyPresent,
                    Self::RemoveKeyNotPresent,
                ])
                .unwrap()
                .clone()
            }
        }

        impl<K> Arbitrary for Mutations<K>
        where
            K: Arbitrary + Ord,
        {
            fn arbitrary(g: &mut Gen) -> Self {
                let mut inserted_keys: Vec<K> = Vec::new();
                let mut mutations = Vec::new();

                while mutations.len() < g.size() {
                    let op: Operation = Operation::arbitrary(g);
                    match op {
                        Operation::InsertKeyPresent if inserted_keys.len() > 0 => {
                            let indexes: Vec<usize> =
                                (0..inserted_keys.len()).into_iter().collect();
                            let k_index = g.choose(&indexes).unwrap();
                            let k = &inserted_keys[*k_index];
                            mutations.push((k.clone(), op));
                        }
                        Operation::InsertKeyNotPresent => {
                            let k = K::arbitrary(g);
                            if let Err(index) = inserted_keys.binary_search(&k) {
                                inserted_keys.insert(index, k.clone());
                                mutations.push((k, op));
                            }
                        }
                        Operation::RemoveKeyPresent if inserted_keys.len() > 0 => {
                            let indexes: Vec<usize> =
                                (0..inserted_keys.len()).into_iter().collect();
                            let k_index = g.choose(&indexes).unwrap();
                            let k = inserted_keys.remove(*k_index);
                            mutations.push((k, op));
                        }
                        Operation::RemoveKeyNotPresent => {
                            let k = K::arbitrary(g);
                            if inserted_keys.binary_search(&k).is_err() {
                                mutations.push((k, op));
                            }
                        }
                        _ => {}
                    }
                }

                Self(mutations)
            }

            fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
                let pop = {
                    let mut clone = self.0.clone();
                    clone.pop();
                    Self(clone)
                };
                let mut v = vec![pop];
                for (i, (k, op)) in self.0.iter().enumerate() {
                    match op {
                        Operation::InsertKeyPresent | Operation::RemoveKeyNotPresent => {
                            let mut clone = self.0.clone();
                            clone.remove(i);
                            v.push(Self(clone));
                        }
                        Operation::RemoveKeyPresent => {
                            let mut clone = self.0.clone();
                            let mut prev = clone[0..i].iter().enumerate().rev();
                            let j = loop {
                                if let Some((j, (k2, op))) = prev.next() {
                                    match op {
                                        Operation::InsertKeyNotPresent if k == k2 => {
                                            break j;
                                        }
                                        _ => {}
                                    }
                                } else {
                                    fail!("No insertion found before")
                                }
                            };
                            clone.remove(i);
                            clone.remove(j);
                            v.push(Self(clone));
                        }
                        _ => {}
                    }
                }

                Box::new(v.into_iter())
            }
        }
    }
}
