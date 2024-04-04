use crate::{
    self as concordium_std, cmp::Ordering, marker::PhantomData, mem, prims, vec::Vec, Deletable,
    Deserial, DeserialWithState, Get, HasStateApi, ParseResult, Read, Serial, Serialize, StateApi,
    StateItemPrefix, StateMap, StateRef, StateRefMut, UnwrapAbort, Write, STATE_ITEM_PREFIX_SIZE,
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
/// The map `StateBTreeMap<K, V, M>` is parametrized by the types:
/// - `K`: Keys used in the map. Most operations on the map require this to
///   implement [`Serialize`](crate::Serialize). Keys cannot contain references
///   to the low-level state, such as types containing
///   [`StateBox`](crate::StateBox), [`StateMap`](crate::StateMap) and
///   [`StateSet`](crate::StateSet).
/// - `V`: Values stored in the map. Most operations on the map require this to
///   implement [`Serial`](crate::Serial) and
///   [`DeserialWithState<StateApi>`](crate::DeserialWithState).
/// - `M`: A `const usize` determining the _minimum degree_ of the B-tree.
///   _Must_ be a value of `2` or above for the tree to work. This can be used
///   to tweak the height of the tree vs size of each node in the tree. The
///   default is set to 8, which seems to perform well on benchmarks. These
///   benchmarks ran operations on a collection of 1000 elements, some using
///   keys of 4 bytes others 16 bytes.
///
/// ## Usage
///
/// New maps can be constructed using the
/// [`new_btree_map`](crate::StateBuilder::new_btree_map) method on the
/// [`StateBuilder`](crate::StateBuilder).
///
/// ```no_run
/// # use concordium_std::*;
/// # let mut state_builder = StateBuilder::open(StateApi::open());
/// /// In an init method:
/// let mut map1 = state_builder.new_btree_map();
/// # map1.insert(0u8, 1u8); // Specifies type of map.
///
/// # let mut host = ExternHost { state: (), state_builder };
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
/// struct MyState {
///     inner: StateBTreeMap<u64, u64>,
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
/// # struct MyState {
/// #    inner: StateBTreeMap<u64, u64>
/// # }
/// fn correct_replace(state_builder: &mut StateBuilder, state: &mut MyState) {
///     state.inner.clear_flat();
/// }
/// ```
/// Or alternatively
/// ```no_run
/// # use concordium_std::*;
/// # struct MyState {
/// #    inner: StateBTreeMap<u64, u64>
/// # }
/// fn correct_replace(state_builder: &mut StateBuilder, state: &mut MyState) {
///     let old_map = mem::replace(&mut state.inner, state_builder.new_btree_map());
///     old_map.delete()
/// }
/// ```
#[derive(Serial)]
pub struct StateBTreeMap<K, V, const M: usize = 8> {
    /// Mapping from key to value.
    /// Each key in this map must also be in the `key_order` set.
    pub(crate) key_value: StateMap<K, V, StateApi>,
    /// A set for tracking the order of the inserted keys.
    /// Each key in this set must also have an associated value in the
    /// `key_value` map.
    pub(crate) key_order: StateBTreeSet<K, M>,
}

impl<const M: usize, K, V> StateBTreeMap<K, V, M> {
    /// Insert a key-value pair into the map.
    /// Returns the previous value if the key was already in the map.
    ///
    /// *Caution*: If `Option<V>` is to be deleted and contains a data structure
    /// prefixed with `State` (such as [StateBox](crate::StateBox) or
    /// [StateMap](crate::StateMap)), then it is important to call
    /// [`Deletable::delete`](crate::Deletable::delete) on the value returned
    /// when you're finished with it. Otherwise, it will remain in the
    /// contract state.
    #[must_use]
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Serialize + Ord,
        V: Serial + DeserialWithState<StateApi>, {
        let old_value_option = self.key_value.insert_borrowed(&key, value);
        if old_value_option.is_none() && !self.key_order.insert(key) {
            // Inconsistency between the map and ordered_set.
            crate::trap();
        }
        old_value_option
    }

    /// Remove a key from the map, returning the value at the key if the key was
    /// previously in the map.
    ///
    /// *Caution*: If `V` is a [StateBox](crate::StateBox),
    /// [StateMap](crate::StateMap), then it is important to call
    /// [`Deletable::delete`](crate::Deletable::delete) on the value returned
    /// when you're finished with it. Otherwise, it will remain in the
    /// contract state.
    #[must_use]
    pub fn remove_and_get(&mut self, key: &K) -> Option<V>
    where
        K: Serialize + Ord,
        V: Serial + DeserialWithState<StateApi> + Deletable, {
        let v = self.key_value.remove_and_get(key);
        if v.is_some() && !self.key_order.remove(key) {
            // Inconsistency between the map and ordered_set.
            crate::trap();
        }
        v
    }

    /// Remove a key from the map.
    /// This also deletes the value in the state.
    pub fn remove(&mut self, key: &K)
    where
        K: Serialize + Ord,
        V: Serial + DeserialWithState<StateApi> + Deletable, {
        if self.key_order.remove(key) {
            self.key_value.remove(key);
        }
    }

    /// Get a reference to the value corresponding to the key.
    pub fn get(&self, key: &K) -> Option<StateRef<V>>
    where
        K: Serialize,
        V: Serial + DeserialWithState<StateApi>, {
        // Minor optimization in the case of the empty collection. Since the length is
        // tracked by the ordered set, we can return early, saving a key lookup.
        if self.key_order.is_empty() {
            None
        } else {
            self.key_value.get(key)
        }
    }

    /// Get a mutable reference to the value corresponding to the key.
    pub fn get_mut(&mut self, key: &K) -> Option<StateRefMut<V, StateApi>>
    where
        K: Serialize,
        V: Serial + DeserialWithState<StateApi>, {
        // Minor optimization in the case of the empty collection. Since the length is
        // tracked by the ordered set, we can return early, saving a key lookup.
        if self.key_order.is_empty() {
            None
        } else {
            self.key_value.get_mut(key)
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    #[inline(always)]
    pub fn contains_key(&self, key: &K) -> bool
    where
        K: Serialize + Ord, {
        self.key_order.contains(key)
    }

    /// Returns the smallest key in the map that is strictly larger than the
    /// provided key. `None` meaning no such key is present in the map.
    #[inline(always)]
    pub fn higher(&self, key: &K) -> Option<StateRef<K>>
    where
        K: Serialize + Ord, {
        self.key_order.higher(key)
    }

    /// Returns the smallest key in the map that is equal or larger than the
    /// provided key. `None` meaning no such key is present in the map.
    #[inline(always)]
    pub fn eq_or_higher(&self, key: &K) -> Option<StateRef<K>>
    where
        K: Serialize + Ord, {
        self.key_order.eq_or_higher(key)
    }

    /// Returns the largest key in the map that is strictly smaller than the
    /// provided key. `None` meaning no such key is present in the map.
    #[inline(always)]
    pub fn lower(&self, key: &K) -> Option<StateRef<K>>
    where
        K: Serialize + Ord, {
        self.key_order.lower(key)
    }

    /// Returns the largest key in the map that is equal or smaller than the
    /// provided key. `None` meaning no such key is present in the map.
    #[inline(always)]
    pub fn eq_or_lower(&self, key: &K) -> Option<StateRef<K>>
    where
        K: Serialize + Ord, {
        self.key_order.eq_or_lower(key)
    }

    /// Returns a reference to the first key in the map, if any. This key is
    /// always the minimum of all keys in the map.
    #[inline(always)]
    pub fn first_key(&self) -> Option<StateRef<K>>
    where
        K: Serialize + Ord, {
        self.key_order.first()
    }

    /// Returns a reference to the last key in the map, if any. This key is
    /// always the maximum of all keys in the map.
    #[inline(always)]
    pub fn last_key(&self) -> Option<StateRef<K>>
    where
        K: Serialize + Ord, {
        self.key_order.last()
    }

    /// Return the number of elements in the map.
    #[inline(always)]
    pub fn len(&self) -> u32 { self.key_order.len() }

    /// Returns `true` is the map contains no elements.
    #[inline(always)]
    pub fn is_empty(&self) -> bool { self.key_order.is_empty() }

    /// Create an iterator over the entries of [`StateBTreeMap`].
    /// Ordered by `K` ascending.
    #[inline(always)]
    pub fn iter(&self) -> StateBTreeMapIter<K, V, M> {
        StateBTreeMapIter {
            key_iter: self.key_order.iter(),
            map:      &self.key_value,
        }
    }

    /// Clears the map, removing all key-value pairs.
    /// This also includes values pointed at, if `V`, for example, is a
    /// [StateBox](crate::StateBox). **If applicable use
    /// [`clear_flat`](Self::clear_flat) instead.**
    pub fn clear(&mut self)
    where
        K: Serialize,
        V: Serial + DeserialWithState<StateApi> + Deletable, {
        self.key_value.clear();
        self.key_order.clear();
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
        K: Serialize,
        V: Serialize, {
        self.key_value.clear_flat();
        self.key_order.clear();
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
/// The map `StateBTreeSet<K, M>` is parametrized by the types:
/// - `K`: Keys used in the set. Most operations on the set require this to
///   implement [`Serialize`](crate::Serialize). Keys cannot contain references
///   to the low-level state, such as types containing
///   [`StateBox`](crate::StateBox), [`StateMap`](crate::StateMap) and
///   [`StateSet`](crate::StateSet).
/// - `M`: A `const usize` determining the _minimum degree_ of the B-tree.
///   _Must_ be a value of `2` or above for the tree to work. This can be used
///   to tweak the height of the tree vs size of each node in the tree. The
///   default is set to 8, which seems to perform well on benchmarks. These
///   benchmarks ran operations on a collection of 1000 elements, some using
///   keys of 4 bytes others 16 bytes.
///
/// ## Usage
///
/// New sets can be constructed using the
/// [`new_btree_set`](crate::StateBuilder::new_btree_set) method on the
/// [`StateBuilder`](crate::StateBuilder).
///
/// ```no_run
/// # use concordium_std::*;
/// # let mut state_builder = StateBuilder::open(StateApi::open());
/// /// In an init method:
/// let mut map1 = state_builder.new_btree_set();
/// # map1.insert(0u8); // Specifies type of map.
/// # let mut host = ExternHost { state: (), state_builder };
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
/// struct MyState {
///     inner: StateBTreeSet<u64>,
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
/// # struct MyState {
/// #    inner: StateBTreeSet<u64>
/// # }
/// fn correct_replace(state_builder: &mut StateBuilder, state: &mut MyState) {
///     state.inner.clear();
/// }
/// ```
pub struct StateBTreeSet<K, const M: usize = 8> {
    /// Type marker for the key.
    _marker_key:  PhantomData<K>,
    /// The unique prefix to use for this map in the key-value store.
    prefix:       StateItemPrefix,
    /// The API for interacting with the low-level state.
    state_api:    StateApi,
    /// The ID of the root node of the tree, where None represents the tree is
    /// empty.
    root:         Option<NodeId>,
    /// Tracking the number of items in the tree.
    len:          u32,
    /// Tracking the next available ID for a new node.
    next_node_id: NodeId,
}

impl<const M: usize, K> StateBTreeSet<K, M> {
    /// Construct a new [`StateBTreeSet`] given a unique prefix to use in the
    /// key-value store.
    pub(crate) fn new(state_api: StateApi, prefix: StateItemPrefix) -> Self {
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
        // new_root now contains one key and two children, so we need to know
        // which one to insert into.
        let key_in_root = unsafe { new_root.keys.get_unchecked(0) };
        let child = if key_in_root < &key {
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
            let child_node_id = unsafe { *node.children.get_unchecked(child_index) };
            node = self.get_node(child_node_id);
        }
    }

    /// Return the number of elements in the set.
    pub fn len(&self) -> u32 { self.len }

    /// Returns `true` is the set contains no elements.
    pub fn is_empty(&self) -> bool { self.root.is_none() }

    /// Get an iterator over the elements in the `StateBTreeSet`. The iterator
    /// returns elements in increasing order.
    pub fn iter(&self) -> StateBTreeSetIter<K, M> {
        StateBTreeSetIter {
            length:            self.len.try_into().unwrap_abort(),
            next_node:         self.root,
            depth_first_stack: Vec::new(),
            tree:              self,
            _marker_lifetime:  Default::default(),
        }
    }

    /// Clears the set, removing all elements.
    pub fn clear(&mut self) {
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

    /// Returns the smallest key in the set that is strictly larger than the
    /// provided key. `None` meaning no such key is present in the set.
    pub fn higher(&self, key: &K) -> Option<StateRef<K>>
    where
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

                let child_node_id = unsafe { *node.children.get_unchecked(higher_key_index) };
                node = self.get_node(child_node_id);
            }
        }
    }

    /// Returns the smallest key in the set that is equal or larger than the
    /// provided key. `None` meaning no such key is present in the set.
    pub fn eq_or_higher(&self, key: &K) -> Option<StateRef<K>>
    where
        K: Serialize + Ord, {
        let Some(root_node_id) = self.root else {
            return None;
        };

        let mut node = self.get_node(root_node_id);
        let mut higher_so_far = None;
        loop {
            let higher_key_index = match node.keys.binary_search(key) {
                Ok(index) => {
                    // This does not mutate the node in the end, just the representation in memory
                    // which is freed after the call.
                    return Some(StateRef::new(node.keys.swap_remove(index)));
                }
                Err(index) => index,
            };

            if node.is_leaf() {
                return if higher_key_index < node.keys.len() {
                    Some(StateRef::new(node.keys.swap_remove(higher_key_index)))
                } else {
                    higher_so_far
                };
            } else {
                if higher_key_index < node.keys.len() {
                    higher_so_far = Some(StateRef::new(node.keys.swap_remove(higher_key_index)))
                }

                let child_node_id = unsafe { *node.children.get_unchecked(higher_key_index) };
                node = self.get_node(child_node_id);
            }
        }
    }

    /// Returns the largest key in the set that is strictly smaller than the
    /// provided key. `None` meaning no such key is present in the set.
    pub fn lower(&self, key: &K) -> Option<StateRef<K>>
    where
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
                    Some(StateRef::new(node.keys.swap_remove(lower_key_index - 1)))
                };
            } else {
                if lower_key_index > 0 {
                    lower_so_far = Some(StateRef::new(node.keys.swap_remove(lower_key_index - 1)));
                }
                let child_node_id = unsafe { node.children.get_unchecked(lower_key_index) };
                node = self.get_node(*child_node_id)
            }
        }
    }

    /// Returns the largest key in the set that is equal or smaller than the
    /// provided key. `None` meaning no such key is present in the set.
    pub fn eq_or_lower(&self, key: &K) -> Option<StateRef<K>>
    where
        K: Serialize + Ord, {
        let Some(root_node_id) = self.root else {
            return None;
        };

        let mut node = self.get_node(root_node_id);
        let mut lower_so_far = None;
        loop {
            let lower_key_index = match node.keys.binary_search(key) {
                Ok(index) => {
                    // This does not mutate the node in the end, just the representation in memory
                    // which is freed after the call.
                    return Some(StateRef::new(node.keys.swap_remove(index)));
                }
                Err(index) => index,
            };

            if node.is_leaf() {
                return if lower_key_index == 0 {
                    lower_so_far
                } else {
                    Some(StateRef::new(node.keys.swap_remove(lower_key_index - 1)))
                };
            } else {
                if lower_key_index > 0 {
                    lower_so_far = Some(StateRef::new(node.keys.swap_remove(lower_key_index - 1)));
                }
                let child_node_id = unsafe { node.children.get_unchecked(lower_key_index) };
                node = self.get_node(*child_node_id)
            }
        }
    }

    /// Returns a reference to the first key in the set, if any. This key is
    /// always the minimum of all keys in the set.
    pub fn first(&self) -> Option<StateRef<K>>
    where
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
        K: Ord + Serialize, {
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
                self.delete_node(root_node_id, root);
                return true;
            }
        }
        // If the root is empty but the tree is not, point to the only child of the root
        // as the root.
        if root.keys.is_empty() {
            self.root = Some(root.children[0]);
            self.delete_node(root_node_id, root);
        }
        deleted_something
    }

    /// Internal function for taking the largest key in a subtree.
    ///
    /// Assumes:
    /// - The provided node is not the root.
    /// - The node contain more than minimum number of keys.
    fn remove_largest_key(&mut self, mut node: StateRefMut<'_, Node<M, K>, StateApi>) -> K
    where
        K: Ord + Serialize, {
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
    fn remove_smallest_key(&mut self, mut node: StateRefMut<'_, Node<M, K>, StateApi>) -> K
    where
        K: Ord + Serialize, {
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
    fn prepare_child_for_key_removal<'c>(
        &mut self,
        mut node: StateRefMut<Node<M, K>, StateApi>,
        index: usize,
    ) -> StateRefMut<'c, Node<M, K>, StateApi>
    where
        K: Ord + Serialize, {
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
        K: Ord + Serialize, {
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
        K: Ord + Serialize, {
        let mut node = self.get_node(node.children[child_index]);
        while !node.is_leaf() {
            let child_node_id = node.children.first().unwrap_abort();
            node = self.get_node(*child_node_id);
        }
        node.keys.swap_remove(0)
    }

    /// Move key at `index` from the node to the lower child and then merges
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
        mut larger_child: StateRefMut<Node<M, K>, StateApi>,
    ) where
        K: Ord + Serialize, {
        let parent_key = parent_node.keys.remove(index);
        let larger_child_id = parent_node.children.remove(index + 1);
        child.keys.push(parent_key);
        child.keys.append(&mut larger_child.keys);
        child.children.append(&mut larger_child.children);
        self.delete_node(larger_child_id, larger_child);
    }

    /// Internal function for constructing a node. It will increment the next
    /// node ID and create an entry in the smart contract key-value store.
    fn create_node<'b>(
        &mut self,
        keys: Vec<K>,
        children: Vec<NodeId>,
    ) -> (NodeId, StateRefMut<'b, Node<M, K>, StateApi>)
    where
        K: Serialize, {
        let node_id = self.next_node_id.fetch_and_add();
        let node = Node {
            keys,
            children,
        };
        let entry = self.state_api.create_entry(&node_id.as_key(&self.prefix)).unwrap_abort();
        let mut ref_mut: StateRefMut<'_, Node<M, K>, StateApi> =
            StateRefMut::new(entry, self.state_api.clone());
        ref_mut.set(node);
        (node_id, ref_mut)
    }

    /// Internal function for deleting a node, removing the entry in the smart
    /// contract key-value store. Traps if no node was present.
    fn delete_node(&mut self, node_id: NodeId, node: StateRefMut<Node<M, K>, StateApi>)
    where
        K: Serial, {
        let key = node_id.as_key(&self.prefix);
        node.drop_without_storing();
        unsafe { prims::state_delete_entry(key.as_ptr(), key.len() as u32) };
    }

    /// Internal function for inserting into a subtree.
    /// Assumes the given node is not full.
    fn insert_non_full(&mut self, initial_node: StateRefMut<Node<M, K>, StateApi>, key: K) -> bool
    where
        K: Serialize + Ord, {
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
            let child_id = unsafe { node.children.get_unchecked(insert_index) };
            let mut child = self.get_node_mut(*child_id);
            node = if !child.is_full() {
                child
            } else {
                let larger_child = self.split_child(&mut node, insert_index, &mut child);
                // Since the child is now split into two, we have to check which one to insert
                // into.
                let moved_up_key = &node.keys[insert_index];
                match moved_up_key.cmp(&key) {
                    Ordering::Equal => return false,
                    Ordering::Less => larger_child,
                    Ordering::Greater => child,
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
    ) -> StateRefMut<'b, Node<M, K>, StateApi>
    where
        K: Serialize + Ord, {
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
        Key: Deserial, {
        let key = node_id.as_key(&self.prefix);
        let mut entry = self.state_api.lookup_entry(&key).unwrap_abort();
        entry.get().unwrap_abort()
    }

    /// Internal function for looking up a node, providing mutable access.
    /// This assumes the node is present and traps if this is not the case.
    fn get_node_mut<'b>(&mut self, node_id: NodeId) -> StateRefMut<'b, Node<M, K>, StateApi>
    where
        K: Serial, {
        let key = node_id.as_key(&self.prefix);
        let entry = self.state_api.lookup_entry(&key).unwrap_abort();
        StateRefMut::new(entry, self.state_api.clone())
    }
}

/// An iterator over the entries of a [`StateBTreeSet`].
///
/// Ordered by `K`.
///
/// This `struct` is created by the [`iter`][StateBTreeSet::iter] method on
/// [`StateBTreeSet`]. See its documentation for more.
pub struct StateBTreeSetIter<'a, 'b, K, const M: usize> {
    /// The number of elements left to iterate.
    length:            usize,
    /// Reference to a node in the tree to load and iterate before the current
    /// node.
    next_node:         Option<NodeId>,
    /// Tracking the nodes depth first, which are currently being iterated.
    depth_first_stack: Vec<(Node<M, KeyWrapper<K>>, usize)>,
    /// Reference to the set, needed for looking up the nodes.
    tree:              &'a StateBTreeSet<K, M>,
    /// Marker for tracking the lifetime of the key.
    _marker_lifetime:  PhantomData<&'b K>,
}

impl<'a, 'b, const M: usize, K> Iterator for StateBTreeSetIter<'a, 'b, K, M>
where
    'a: 'b,
    K: Deserial,
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

        let (node, index) = self.depth_first_stack.last_mut()?;
        let key = node.keys[*index].key.take().unwrap_abort();
        *index += 1;
        let no_more_keys = index == &node.keys.len();
        if !node.is_leaf() {
            let child_id = node.children[*index];
            self.next_node = Some(child_id);
        }
        if no_more_keys {
            // This was the last key in the node, so remove the node from the stack.
            let _ = self.depth_first_stack.pop();
        }
        self.length -= 1;
        Some(StateRef::new(key))
    }

    fn size_hint(&self) -> (usize, Option<usize>) { (self.length, Some(self.length)) }
}

/// An iterator over the entries of a [`StateBTreeMap`].
///
/// Ordered by `K`.
///
/// This `struct` is created by the [`iter`][StateBTreeMap::iter] method on
/// [`StateBTreeMap`]. See its documentation for more.
pub struct StateBTreeMapIter<'a, 'b, K, V, const M: usize> {
    /// Iterator over the keys in the map.
    key_iter: StateBTreeSetIter<'a, 'b, K, M>,
    /// Reference to the map holding the values.
    map:      &'a StateMap<K, V, StateApi>,
}

impl<'a, 'b, const M: usize, K, V> Iterator for StateBTreeMapIter<'a, 'b, K, V, M>
where
    'a: 'b,
    K: Serialize,
    V: Serial + DeserialWithState<StateApi> + 'b,
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
/// node is stored in the smart contract key-value store.
#[derive(Debug, Copy, Clone, Serialize)]
#[repr(transparent)]
struct NodeId {
    id: u64,
}

/// Byte size of the key used to store a BTree internal node in the smart
/// contract key-value store.
const BTREE_NODE_KEY_SIZE: usize = STATE_ITEM_PREFIX_SIZE + NodeId::SERIALIZED_BYTE_SIZE;

impl NodeId {
    /// Byte size of `NodeId` when serialized.
    const SERIALIZED_BYTE_SIZE: usize = 8;

    /// Return a copy of the NodeId, then increments itself.
    fn fetch_and_add(&mut self) -> Self {
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
        for (place, value) in prefixed.iter_mut().zip(prefix) {
            place.write(*value);
        }
        let id_bytes = self.id.to_le_bytes();
        for (place, value) in prefixed[STATE_ITEM_PREFIX_SIZE..].iter_mut().zip(id_bytes) {
            place.write(value);
        }
        // Transmuting away the maybeuninit is safe since we have initialized all of
        // them.
        unsafe { mem::transmute(prefixed) }
    }
}

/// Type representing a node in the [`StateBTreeMap`].
/// Each node is stored separately in the smart contract key-value store.
#[derive(Debug, Serialize)]
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

    /// Check if the node holds the maximum number of keys.
    #[inline(always)]
    fn is_full(&self) -> bool { self.keys.len() == Self::MAXIMUM_KEY_LEN }

    /// Check if the node is representing a leaf in the tree.
    #[inline(always)]
    fn is_leaf(&self) -> bool { self.children.is_empty() }

    /// Check if the node holds the minimum number of keys.
    #[inline(always)]
    fn is_at_min(&self) -> bool { self.keys.len() == Self::MINIMUM_KEY_LEN }
}

/// Wrapper implement the exact same deserial as K, but wraps it in an
/// option in memory. This is used to allow taking a key from a mutable
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

impl<const M: usize, K> Serial for StateBTreeSet<K, M> {
    fn serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.prefix.serial(out)?;
        self.root.serial(out)?;
        self.len.serial(out)?;
        self.next_node_id.serial(out)
    }
}

impl<const M: usize, K> DeserialWithState<StateApi> for StateBTreeSet<K, M> {
    fn deserial_with_state<R: Read>(state: &StateApi, source: &mut R) -> ParseResult<Self> {
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

impl<const M: usize, K, V> DeserialWithState<StateApi> for StateBTreeMap<K, V, M> {
    fn deserial_with_state<R: Read>(state: &StateApi, source: &mut R) -> ParseResult<Self> {
        let key_value = StateMap::deserial_with_state(state, source)?;
        let key_order = StateBTreeSet::deserial_with_state(state, source)?;
        Ok(Self {
            key_value,
            key_order,
        })
    }
}

impl<const M: usize, K, V> Deletable for StateBTreeMap<K, V, M>
where
    K: Serialize,
    V: Serial + DeserialWithState<StateApi> + Deletable,
{
    fn delete(mut self) { self.clear(); }
}

/// This test module relies on the runtime providing host functions and can only
/// be run using `cargo concordium test`.
#[cfg(feature = "internal-wasm-test")]
mod wasm_test_btree {
    use super::*;
    use crate::{claim, claim_eq, concordium_test, StateApi, StateBuilder};

    /// The invariants to check in a btree.
    /// Should only be used while debugging and testing the btree itself.
    #[derive(Debug)]
    pub(crate) enum InvariantViolation {
        /// The collection has length above 0, but no root.
        NonZeroLenWithNoRoot,
        /// The collection contain a root node, but this has no keys.
        ZeroKeysInRoot,
        /// Iterating the keys in the entire collection, is not in strictly
        /// ascending order.
        IterationOutOfOrder,
        /// Leaf node found at different depths.
        LeafAtDifferentDepth,
        /// The keys in a node are not in strictly ascending order.
        NodeKeysOutOfOrder,
        /// The non-leaf node does not contain `keys.len() + 1` children.
        MismatchingChildrenLenKeyLen,
        /// The non-root node contains fewer keys than the minimum.
        KeysLenBelowMin,
        /// The non-root node contains more keys than the maximum.
        KeysLenAboveMax,
        /// The leaf node contains children nodes.
        LeafWithChildren,
        /// The non-root non-leaf node contains fewer children than the minimum.
        ChildrenLenBelowMin,
        /// The non-root non-leaf node contains more children than the maximum.
        ChildrenLenAboveMax,
    }

    impl<K, const M: usize> StateBTreeSet<K, M> {
        /// Check invariants, producing an error if any of them are
        /// violated.
        /// See [`InvariantViolation`] for the of list invariants being checked.
        /// Should only be used while debugging and testing the btree itself.
        fn check_invariants(&self) -> Result<(), InvariantViolation>
        where
            K: Serialize + Ord, {
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

            for i in 1..root.keys.len() {
                if &root.keys[i - 1] >= &root.keys[i] {
                    return Err(InvariantViolation::NodeKeysOutOfOrder);
                }
            }
            if root.keys.len() > Node::<M, K>::MAXIMUM_KEY_LEN {
                return Err(InvariantViolation::KeysLenAboveMax);
            }

            if root.is_leaf() {
                if !root.children.is_empty() {
                    return Err(InvariantViolation::LeafWithChildren);
                }
            } else {
                if root.children.len() != root.keys.len() + 1 {
                    return Err(InvariantViolation::MismatchingChildrenLenKeyLen);
                }
                if root.children.len() > Node::<M, K>::MAXIMUM_CHILD_LEN {
                    return Err(InvariantViolation::ChildrenLenAboveMax);
                }
            }

            let mut stack = vec![(0usize, root.children)];
            let mut leaf_depth = None;
            while let Some((node_level, mut nodes)) = stack.pop() {
                while let Some(node_id) = nodes.pop() {
                    let node: Node<M, K> = self.get_node(node_id);
                    node.check_invariants()?;
                    if node.is_leaf() {
                        let depth = leaf_depth.get_or_insert(node_level);
                        if *depth != node_level {
                            return Err(InvariantViolation::LeafAtDifferentDepth);
                        }
                    } else {
                        stack.push((node_level + 1, node.children));
                    }
                }
            }

            let mut prev = None;
            for key in self.iter() {
                if let Some(p) = prev.as_deref() {
                    if p > key.deref() {
                        return Err(InvariantViolation::IterationOutOfOrder);
                    }
                }
                prev = Some(key);
            }
            Ok(())
        }

        /// Construct a string for displaying the btree and debug information.
        /// Should only be used while debugging and testing the btree itself.
        pub(crate) fn debug(&self) -> String
        where
            K: Serialize + std::fmt::Debug + Ord, {
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
    }

    impl<const M: usize, K> Node<M, K> {
        /// Check invariants of a non-root node in a btree, producing an error
        /// if any of them are violated.
        /// See [`InvariantViolation`] for the of list invariants being checked.
        /// Should only be used while debugging and testing the btree itself.
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
                if self.children.len() != self.keys.len() + 1 {
                    return Err(InvariantViolation::MismatchingChildrenLenKeyLen);
                }
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

    /// Insert `2 * M` items such that the btree contains more than the root
    /// node. Checking that every item is contained in the collection.
    #[concordium_test]
    fn test_btree_insert_asc_above_max_branching_degree() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        const M: usize = 5;
        let mut tree = state_builder.new_btree_set_degree::<M, _>();
        let items = (2 * M) as u32;
        for n in 0..items {
            claim!(tree.insert(n));
        }
        for n in 0..items {
            claim!(tree.contains(&n));
        }
        claim_eq!(tree.len(), items)
    }

    /// Insert items such that the btree must be at least height 3 to contain
    /// all of them. With a minimum degree of 2, each node can contain up to
    /// 3 items and have 4 children, meaning 16 items is needed.
    /// Then checks that every item is contained in the collection.
    #[concordium_test]
    fn test_btree_insert_asc_height_3() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..16 {
            claim!(tree.insert(n));
        }
        for n in 0..16 {
            claim!(tree.contains(&n));
        }
        claim_eq!(tree.len(), 16);
        claim!(!tree.contains(&17));
    }

    /// Insert items in a random order.
    /// Then checks that every item is contained in the collection.
    #[concordium_test]
    fn test_btree_insert_random_order() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();

        tree.insert(0);
        tree.insert(3);
        tree.insert(2);
        tree.insert(1);
        tree.insert(5);
        tree.insert(7);
        tree.insert(6);
        tree.insert(4);

        for n in 0..=7 {
            claim!(tree.contains(&n));
        }
        claim_eq!(tree.len(), 8)
    }

    /// Build a set and query `higher` on each key plus some keys outside of the
    /// set.
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
        claim_eq!(tree.higher(&0).as_deref(), Some(&1));
        claim_eq!(tree.higher(&1).as_deref(), Some(&2));
        claim_eq!(tree.higher(&2).as_deref(), Some(&3));
        claim_eq!(tree.higher(&3).as_deref(), Some(&4));
        claim_eq!(tree.higher(&4).as_deref(), Some(&5));
        claim_eq!(tree.higher(&5).as_deref(), Some(&7));
        claim_eq!(tree.higher(&6).as_deref(), Some(&7));
        claim_eq!(tree.higher(&7).as_deref(), None);
        claim_eq!(tree.higher(&8).as_deref(), None);
    }

    /// Build a set and query `lower` on each key plus some keys outside of the
    /// set.
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
        claim_eq!(tree.lower(&0).as_deref(), None);
        claim_eq!(tree.lower(&1).as_deref(), None);
        claim_eq!(tree.lower(&2).as_deref(), Some(&1));
        claim_eq!(tree.lower(&3).as_deref(), Some(&2));
        claim_eq!(tree.lower(&4).as_deref(), Some(&3));
        claim_eq!(tree.lower(&5).as_deref(), Some(&4));
        claim_eq!(tree.lower(&6).as_deref(), Some(&5));
        claim_eq!(tree.lower(&7).as_deref(), Some(&5));
        claim_eq!(tree.lower(&8).as_deref(), Some(&7));
    }

    /// Build a set and query `eq_or_higher` on each key plus some keys outside
    /// of the set.
    #[concordium_test]
    fn test_btree_eq_or_higher() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree.insert(4);
        tree.insert(5);
        tree.insert(7);
        claim_eq!(tree.eq_or_higher(&0).as_deref(), Some(&1));
        claim_eq!(tree.eq_or_higher(&1).as_deref(), Some(&1));
        claim_eq!(tree.eq_or_higher(&2).as_deref(), Some(&2));
        claim_eq!(tree.eq_or_higher(&3).as_deref(), Some(&3));
        claim_eq!(tree.eq_or_higher(&4).as_deref(), Some(&4));
        claim_eq!(tree.eq_or_higher(&5).as_deref(), Some(&5));
        claim_eq!(tree.eq_or_higher(&6).as_deref(), Some(&7));
        claim_eq!(tree.eq_or_higher(&7).as_deref(), Some(&7));
        claim_eq!(tree.eq_or_higher(&8).as_deref(), None);
    }

    /// Build a set and query `eq_or_lower` on each key plus some keys outside
    /// of the set.
    #[concordium_test]
    fn test_btree_eq_or_lower() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree.insert(4);
        tree.insert(5);
        tree.insert(7);
        claim_eq!(tree.eq_or_lower(&0).as_deref(), None);
        claim_eq!(tree.eq_or_lower(&1).as_deref(), Some(&1));
        claim_eq!(tree.eq_or_lower(&2).as_deref(), Some(&2));
        claim_eq!(tree.eq_or_lower(&3).as_deref(), Some(&3));
        claim_eq!(tree.eq_or_lower(&4).as_deref(), Some(&4));
        claim_eq!(tree.eq_or_lower(&5).as_deref(), Some(&5));
        claim_eq!(tree.eq_or_lower(&6).as_deref(), Some(&5));
        claim_eq!(tree.eq_or_lower(&7).as_deref(), Some(&7));
        claim_eq!(tree.eq_or_lower(&8).as_deref(), Some(&7));
    }

    /// Insert a large number of items.
    /// Check the set contains each item.
    /// Insert the same items again, checking the set is the same size
    /// afterwards.
    #[concordium_test]
    fn test_btree_insert_a_lot_then_reinsert() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..500 {
            claim!(tree.insert(n));
        }
        for n in (500..1000).into_iter().rev() {
            claim!(tree.insert(n));
        }

        for n in 0..1000 {
            claim!(tree.contains(&n))
        }
        claim_eq!(tree.len(), 1000);

        for n in 0..1000 {
            claim!(!tree.insert(n))
        }
        claim_eq!(tree.len(), 1000)
    }

    /// Remove from a btree with only the root node.
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

    /// Removing from a the lower child node which is at minimum keys, causing a
    /// merge.
    ///
    /// - Builds a tree of the form: [[0], 1, [2]]
    /// - Remove 0
    /// - Expecting a tree of the form: [1, 2]
    #[concordium_test]
    fn test_btree_remove_only_key_lower_leaf_in_three_node() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..4 {
            tree.insert(n);
        }
        tree.remove(&3);

        claim!(tree.remove(&0));

        claim!(!tree.contains(&0));
        claim!(tree.contains(&1));
        claim!(tree.contains(&2));
    }

    /// Removing from a the higher child node which is at minimum keys, causing
    /// a merge.
    ///
    /// - Builds a tree of the form: [[0], 1, [2]]
    /// - Remove 2
    /// - Expecting a tree of the form: [0, 1]
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

    /// Removing from a the higher child node which is at minimum keys, causing
    /// it to move a key from its higher sibling.
    ///
    /// - Builds a tree of the form: [[0, 1], 2, [3]]
    /// - Remove 3
    /// - Expecting a tree of the form: [[0], 1, [2]]
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

    /// Removing from a the higher child node which is at minimum keys, causing
    /// it to move a key from its lower sibling.
    ///
    /// - Builds a tree of the form: [[0], 1, [2, 3]]
    /// - Remove 0
    /// - Expecting a tree of the form: [[1], 2, [3]]
    #[concordium_test]
    fn test_btree_remove_from_lower_leaf_in_three_node_taking_from_sibling() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..4 {
            tree.insert(n);
        }
        claim!(tree.remove(&0));

        claim!(!tree.contains(&0));
        claim!(tree.contains(&1));
        claim!(tree.contains(&2));
        claim!(tree.contains(&3));
    }

    /// Removing from a the root node which is at minimum keys, likewise are the
    /// children, causing a merge.
    ///
    /// - Builds a tree of the form: [[0], 1, [2]]
    /// - Remove 1
    /// - Expecting a tree of the form: [0, 2]
    #[concordium_test]
    fn test_btree_remove_from_root_in_three_node_causing_merge() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in 0..4 {
            tree.insert(n);
        }
        tree.remove(&3);
        claim!(tree.remove(&1));

        claim!(tree.contains(&0));
        claim!(!tree.contains(&1));
        claim!(tree.contains(&2));
    }

    /// Removing from a the root node which is at minimum keys, taking a child
    /// from its higher child.
    ///
    /// - Builds a tree of the form: [[0], 1, [2, 3]]
    /// - Remove 1
    /// - Expecting a tree of the form: [[0], 2, [3]]
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

    /// Removing from a the root node which is at minimum keys, taking a child
    /// from its lower child.
    ///
    /// - Builds a tree of the form: [[0, 1], 2, [3]]
    /// - Remove 2
    /// - Expecting a tree of the form: [[0], 1, [3]]
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

    /// Test iteration of the set.
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

    /// Testcase for duplicate keys in the set. Due to an edge case where the
    /// key moved up as part of splitting a child node, is equal to the
    /// inserted key.
    ///
    /// - Builds a tree of the form: [[0, 1, 2], 3, [4]]
    /// - Insert 1 (again) causing the [0, 1, 2] to split, moving 1 up to the
    ///   root.
    /// - Expecting a tree of the form: [[0], 1, [2], 3, [4]]
    #[concordium_test]
    fn test_btree_insert_present_key() {
        let mut state_builder = StateBuilder::open(StateApi::open());
        let mut tree = state_builder.new_btree_set_degree::<2, _>();
        for n in [0, 3, 4, 1, 2].into_iter() {
            tree.insert(n);
        }
        claim!(!tree.insert(1));
    }

    // The module is using `concordium_quickcheck` which is located in a deprecated
    // module.
    #[allow(deprecated)]
    mod quickcheck {
        use super::super::*;
        use crate::{
            self as concordium_std, concordium_quickcheck, concordium_test, fail, StateApi,
            StateBuilder, StateError,
        };
        use ::quickcheck::{Arbitrary, Gen, TestResult};

        /// Quickcheck inserting random items, check invariants on the tree and
        /// query every item ensuring the tree contains it.
        #[concordium_quickcheck]
        fn quickcheck_btree_inserts(items: Vec<u32>) -> TestResult {
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

        /// Quickcheck inserting random items and then clear the entire tree
        /// again. Use state api to ensure the btree nodes are no longer
        /// stored in the state.
        #[concordium_quickcheck]
        fn quickcheck_btree_clear(items: Vec<u32>) -> TestResult {
            let mut state_builder = StateBuilder::open(StateApi::open());
            let mut tree = state_builder.new_btree_set_degree::<2, _>();
            for k in items.clone() {
                tree.insert(k);
            }
            tree.clear();
            for k in items.iter() {
                if tree.contains(k) {
                    return TestResult::error(format!("Found {k} in a cleared btree"));
                }
            }

            let state_api = StateApi::open();
            match state_api.iterator(&tree.prefix) {
                Ok(node_iter) => {
                    let nodes_in_state = node_iter.count();
                    TestResult::error(format!(
                        "Found {} nodes still stored in the state",
                        nodes_in_state
                    ))
                }
                Err(StateError::SubtreeWithPrefixNotFound) => TestResult::passed(),
                Err(err) => {
                    TestResult::error(format!("Failed to get iterator for btree nodes: {err:?}"))
                }
            }
        }

        /// Quickcheck inserting random items, then we call query the tree for
        /// higher and lower of every item validating the outcome.
        #[concordium_quickcheck(num_tests = 100)]
        fn quickcheck_btree_iter(mut items: Vec<u32>) -> TestResult {
            let mut state_builder = StateBuilder::open(StateApi::open());
            let mut tree = state_builder.new_btree_set_degree::<2, _>();
            for k in items.clone() {
                tree.insert(k);
            }
            if let Err(violation) = tree.check_invariants() {
                return TestResult::error(format!("Invariant violated: {:?}", violation));
            }

            items.sort();
            items.dedup();

            for (value, expected) in tree.iter().zip(items.into_iter()) {
                if *value != expected {
                    return TestResult::error(format!("Got {} but expected {expected}", *value));
                }
            }

            TestResult::passed()
        }

        /// Quickcheck inserting random items, then we call query the tree for
        /// higher and lower of every item validating the outcome.
        #[concordium_quickcheck(num_tests = 100)]
        fn quickcheck_btree_higher_lower(mut items: Vec<u32>) -> TestResult {
            let mut state_builder = StateBuilder::open(StateApi::open());
            let mut tree = state_builder.new_btree_set_degree::<2, _>();
            for k in items.clone() {
                tree.insert(k);
            }
            if let Err(violation) = tree.check_invariants() {
                return TestResult::error(format!("Invariant violated: {:?}", violation));
            }

            items.sort();
            items.dedup();
            for window in items.windows(2) {
                let l = &window[0];
                let r = &window[1];
                let l_higher = tree.higher(l);
                if l_higher.as_deref() != Some(r) {
                    return TestResult::error(format!(
                        "higher({l}) gave {:?} instead of the expected Some({r})",
                        l_higher.as_deref()
                    ));
                }
                let r_lower = tree.lower(r);
                if r_lower.as_deref() != Some(l) {
                    return TestResult::error(format!(
                        "lower({r}) gave {:?} instead of the expected Some({l})",
                        r_lower.as_deref()
                    ));
                }

                let space_between = r - l > 1;
                if space_between {
                    let l_eq_or_higher = tree.eq_or_higher(&(l + 1));
                    if l_eq_or_higher.as_deref() != Some(r) {
                        return TestResult::error(format!(
                            "eq_or_higher({}) gave {:?} instead of the expected Some({r})",
                            l + 1,
                            l_higher.as_deref()
                        ));
                    }
                }

                if space_between {
                    let r_eq_or_lower = tree.eq_or_lower(&(r - 1));
                    if r_eq_or_lower.as_deref() != Some(l) {
                        return TestResult::error(format!(
                            "eq_or_lower({}) gave {:?} instead of the expected Some({l})",
                            r - 1,
                            l_higher.as_deref()
                        ));
                    }
                }
            }

            if let Some(first) = items.first() {
                let lower = tree.lower(first);
                if lower.is_some() {
                    return TestResult::error(format!(
                        "lower({first}) gave {:?} instead of the expected None",
                        lower.as_deref()
                    ));
                }
            }

            if let Some(last) = items.last() {
                let higher = tree.higher(last);
                if higher.is_some() {
                    return TestResult::error(format!(
                        "higher({last}) gave {:?} instead of the expected None",
                        higher.as_deref()
                    ));
                }
            }

            TestResult::passed()
        }

        /// Quickcheck random mutations see `Mutations` and `run_mutations` for
        /// the details.
        #[concordium_quickcheck(num_tests = 500)]
        fn quickcheck_btree_inserts_removes(mutations: Mutations<u32>) -> TestResult {
            let mut state_builder = StateBuilder::open(StateApi::open());
            let mut tree = state_builder.new_btree_set_degree::<2, _>();

            if let Err(err) = run_mutations(&mut tree, &mutations.mutations) {
                TestResult::error(format!("Error: {}, tree: {}", err, tree.debug()))
            } else {
                TestResult::passed()
            }
        }

        /// Newtype wrapper for Vec to implement Arbitrary.
        #[derive(Debug, Clone)]
        struct Mutations<K> {
            expected_keys: crate::collections::BTreeSet<K>,
            mutations:     Vec<(K, Operation)>,
        }

        /// The different mutating operations to generate for the btree.
        #[derive(Debug, Clone, Copy)]
        enum Operation {
            /// Insert a new key in the set.
            InsertKeyNotPresent,
            /// Insert a key already in the set.
            InsertKeyPresent,
            /// Remove a key in the set.
            RemoveKeyPresent,
            /// Remove a key not already in the set.
            RemoveKeyNotPresent,
        }

        /// Run a list of mutations on a btree, checking the return value and
        /// tree invariants using `StateBTreeSet::check_invariants`
        /// between each mutation, returning an error string if violated.
        fn run_mutations<const M: usize>(
            tree: &mut StateBTreeSet<u32, M>,
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
                // Tracking the keys expected in the set at the point of each mutation.
                // This is used to ensure operations such as inserting and removing a key which
                // is present are actually valid.
                let mut inserted_keys: Vec<K> = Vec::new();
                // The generated mutations to return.
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

                Self {
                    expected_keys: crate::collections::BTreeSet::from_iter(
                        inserted_keys.into_iter(),
                    ),
                    mutations,
                }
            }

            /// We attempt to produce several shrinked versions:
            ///
            /// - Simply remove the last mutation from the list of mutations.
            /// - Remove mutations, which are not adding or removing keys
            ///   (Remove non-present keys and inserting present keys), note
            ///   these might still mutate the internal structure.
            /// - Iterate the mutations and when a key is removed, we traverse
            ///   back in the mutations and remove other mutations of the same
            ///   key back to when it was inserted.
            fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
                let pop = {
                    let mut clone = self.clone();
                    clone.mutations.pop();
                    clone
                };
                let mut v = vec![pop];
                for (i, (k, op)) in self.mutations.iter().enumerate() {
                    match op {
                        Operation::InsertKeyPresent | Operation::RemoveKeyNotPresent => {
                            let mut clone = self.clone();
                            clone.mutations.remove(i);
                            v.push(clone);
                        }
                        Operation::RemoveKeyPresent => {
                            let mut clone = self.clone();
                            let mut prev = self.mutations[0..i].iter().enumerate().rev();
                            clone.mutations.remove(i);
                            clone.expected_keys.remove(k);
                            loop {
                                if let Some((j, (k2, op))) = prev.next() {
                                    match op {
                                        Operation::InsertKeyPresent if k == k2 => {
                                            clone.mutations.remove(j);
                                        }
                                        Operation::InsertKeyNotPresent if k == k2 => {
                                            clone.mutations.remove(j);
                                            break;
                                        }
                                        _ => {}
                                    }
                                } else {
                                    fail!("No insertion found before")
                                }
                            }
                            v.push(clone);
                        }
                        _ => {}
                    }
                }

                Box::new(v.into_iter())
            }
        }
    }
}
