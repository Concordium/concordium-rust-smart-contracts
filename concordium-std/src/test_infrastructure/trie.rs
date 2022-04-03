use super::{TestStateEntry, TestStateEntryData};
use crate::{
    cell::{Cell, RefCell},
    collections::{btree_map, BTreeMap, HashMap as Map, VecDeque},
    rc::Rc,
    Box, StateEntryId, StateError, Vec,
};

const BRANCHING_FACTOR: usize = 16;

pub(crate) type Index = usize;

#[derive(Debug)]
pub(crate) struct StateTrie {
    nodes:           Node,
    next_entry_id:   Cell<StateEntryId>,
    entry_map:       RefCell<Map<StateEntryId, Vec<Index>>>,
    iterator_counts: RefCell<BTreeMap<Vec<Index>, u32>>,
}

impl Default for StateTrie {
    /// Creates an empty state trie.
    fn default() -> Self { Self::new() }
}

fn to_indexes(key: &[u8]) -> Vec<Index> {
    let mut indexes = Vec::new();
    for byte in key {
        indexes.push(((byte & 0b_11_11_00_00) >> 4) as Index);
        indexes.push((byte & 0b_00_00_11_11) as Index);
    }
    indexes
}

/// The inverse of `to_indexes`.
fn from_indexes(indexes: &[Index]) -> Vec<u8> {
    let mut key = Vec::new();
    for chunk in indexes.chunks(2) {
        let n = (chunk[0] << 4 | chunk[1]) as u8;
        key.push(n);
    }
    key
}

impl StateTrie {
    pub(crate) fn new() -> Self {
        Self {
            nodes:           Node::new(),
            next_entry_id:   Cell::new(0),
            entry_map:       RefCell::new(Map::default()),
            iterator_counts: Default::default(),
        }
    }

    /// Construct a `TestStateEntry` and use interior mutation to add increment
    /// next_entry_id and add the entry to the entry_map.
    fn construct_state_entry_test(
        &self,
        indexes: Vec<Index>,
        data: Rc<RefCell<TestStateEntryData>>,
        key: Vec<u8>,
    ) -> TestStateEntry {
        // Get the current next_entry_id
        let state_entry_id = self.next_entry_id.get();

        // Add the id and indexes to the map and increment the next_entry_id
        self.entry_map.borrow_mut().insert(state_entry_id, indexes);
        self.next_entry_id.set(state_entry_id + 1);

        TestStateEntry::open(data, key, state_entry_id)
    }

    pub(crate) fn delete_prefix(&mut self, prefix: &[u8]) -> Result<bool, StateError> {
        let indexes = to_indexes(prefix);
        if self.is_locked(&indexes) {
            return Err(StateError::SubtreeLocked);
        }

        // Unwrapping is safe, because the subtree isn't locked.
        // TODO: Getting an iterator is not OK here due to the bound.
        let iterator = match self.iterator(prefix) {
            Err(StateError::SubtreeWithPrefixNotFound) => {
                return Ok(false);
            }
            Err(e) => crate::fail!("Unexpected error in delete_prefix: {:?}", e),
            Ok(v) => v,
        };

        // Invalidate all the data in the deleted entries such that reading and writing
        // them will fail.
        // Invalidating is necessary because the data is kept alive in any entries given
        // out due to the Rc. This uses the queue iter because Iterator isn't
        // implemented for &Iter and we need to delete the iterator afterwards.
        for entry in iterator.queue.iter() {
            *entry.cursor.data.borrow_mut() = TestStateEntryData::EntryDeleted;
        }
        self.delete_iterator(iterator);

        // Delete the nodes in the tree.
        self.nodes.delete_prefix(&indexes, false)?;
        Ok(true)
    }

    /// Returns true if the subtree corresponding to the given key is
    /// already locked by an existing iterator, false otherwise.
    fn is_locked(&self, prefix: &[usize]) -> bool {
        self.iterator_counts.borrow().keys().any(|p| {
            let shortest = crate::cmp::min(p.len(), prefix.len());
            p[..shortest] == prefix[..shortest]
        })
    }

    pub(crate) fn create_entry(&mut self, key: &[u8]) -> Result<TestStateEntry, StateError> {
        let indexes = to_indexes(key);
        if self.is_locked(&indexes) {
            return Err(StateError::SubtreeLocked);
        }
        let data = self.nodes.create(&indexes);
        let entry = self.construct_state_entry_test(indexes, data, key.to_vec());
        Ok(entry)
    }

    pub(crate) fn lookup(&self, key: &[u8]) -> Option<TestStateEntry> {
        let indexes = to_indexes(key);
        self.nodes
            .lookup(&indexes)
            .map(|data| self.construct_state_entry_test(indexes, data, key.to_vec()))
    }

    pub(crate) fn delete_entry(&mut self, entry: TestStateEntry) -> Result<(), StateError> {
        let indexes = to_indexes(&entry.key);
        if self.is_locked(&indexes) {
            return Err(StateError::SubtreeLocked);
        }
        match self.entry_map.borrow_mut().remove(&entry.state_entry_id) {
            Some(indexes) => self.nodes.delete_data(&indexes),
            None => Err(StateError::EntryNotFound), /* Entry did not exist. Only happens
                                                     * when entry was deleted using
                                                     * delete_prefix. */
        }
    }

    pub(crate) fn iterator(&self, prefix: &[u8]) -> Result<TestStateIter, StateError> {
        let index_prefix = to_indexes(prefix);

        // Try to find the root_node for the prefix.
        let node =
            self.nodes.lookup_node(&index_prefix).ok_or(StateError::SubtreeWithPrefixNotFound)?;

        // Keep track of the number of iterators given out.
        match self.iterator_counts.borrow_mut().entry(index_prefix.clone()) {
            btree_map::Entry::Vacant(vac) => {
                let _ = vac.insert(1);
            }
            btree_map::Entry::Occupied(ref mut occ) => {
                if *occ.get() == u32::MAX {
                    return Err(StateError::IteratorLimitForPrefixExceeded);
                }
                *occ.get_mut() += 1;
            }
        }

        let iter = TestStateIter::new(self, index_prefix, node);
        Ok(iter)
    }

    pub(crate) fn delete_iterator(&mut self, iterator: TestStateIter) {
        match self.iterator_counts.borrow_mut().entry(iterator.prefix) {
            btree_map::Entry::Vacant(_) => crate::fail!(), // Internal error: Should never happen.
            btree_map::Entry::Occupied(mut occ) => {
                if *occ.get() == 1 {
                    // Deleting last iterator for the prefix.
                    occ.remove();
                } else {
                    *occ.get_mut() -= 1;
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct TestStateIter {
    // Only used when deleting the iterator.
    prefix: Vec<Index>,
    queue:  VecDeque<TestStateEntry>,
}

impl TestStateIter {
    fn new(trie: &StateTrie, mut root_index: Vec<Index>, root_of_iter: &Node) -> Self {
        let mut queue = VecDeque::new();
        let prefix = root_index.clone();

        fn build_queue(
            trie: &StateTrie,
            queue: &mut VecDeque<TestStateEntry>,
            indexes: &mut Vec<Index>,
            node: &Node,
        ) {
            for idx in 0..BRANCHING_FACTOR {
                if let Some(child) = &node.children[idx] {
                    // Push current index.
                    indexes.push(idx);

                    if let Some(data) = &child.data {
                        let state_entry = trie.construct_state_entry_test(
                            indexes.clone(),
                            Rc::clone(data),
                            from_indexes(indexes),
                        );
                        queue.push_back(state_entry);
                    }
                    build_queue(trie, queue, indexes, child);

                    // Pop current index again.
                    indexes.pop();
                }
            }
        }

        build_queue(trie, &mut queue, &mut root_index, root_of_iter);
        Self {
            prefix,
            queue,
        }
    }
}

impl Iterator for TestStateIter {
    type Item = TestStateEntry;

    fn next(&mut self) -> Option<Self::Item> { self.queue.pop_front() }
}

#[derive(Debug)]
struct Node {
    data:     Option<Rc<RefCell<TestStateEntryData>>>,
    children: [Option<Box<Node>>; BRANCHING_FACTOR],
}

impl Node {
    fn new() -> Self {
        Self {
            data:     None,
            children: Default::default(),
        }
    }

    /// Tries to find the data in a node with the given index.
    /// Returns `None` if the node doesn't exist or if it doesn't have any data.
    /// Note: If `Some` is returned, it will _always_ be a
    /// `TestStateEntryData::EntryExists(..)`.
    fn lookup(&self, indexes: &[Index]) -> Option<Rc<RefCell<TestStateEntryData>>> {
        self.lookup_node(indexes).and_then(|node| node.data.as_ref().map(Rc::clone))
    }

    /// Tries to find the node with the given index.
    /// Returns `None` if the node doesn't exist.
    fn lookup_node(&self, indexes: &[Index]) -> Option<&Self> {
        match indexes.first() {
            Some(idx) => {
                self.children[*idx].as_ref().and_then(|node| node.lookup_node(&indexes[1..]))
            }
            None => Some(self),
        }
    }

    /// Create a new entry.
    /// It will always return `TestStateEntryData::EntryExists(..)`.
    fn create(&mut self, indexes: &[Index]) -> Rc<RefCell<TestStateEntryData>> {
        match indexes.first() {
            Some(idx) => {
                self.children[*idx].get_or_insert(Box::new(Self::new())).create(&indexes[1..])
            }
            None => {
                let new_data = Rc::new(RefCell::new(TestStateEntryData::new()));
                let new_data_clone = Rc::clone(&new_data);
                self.data = Some(new_data);
                new_data_clone
            }
        }
    }

    fn delete_data(&mut self, indexes: &[Index]) -> Result<(), StateError> {
        self.delete_prefix(indexes, true)
    }

    /// Delete nodes with the given prefix. If `exact`, then it only deletes the
    /// data in the node with that specific key (prefix).
    fn delete_prefix(&mut self, prefix: &[Index], exact: bool) -> Result<(), StateError> {
        match prefix.first() {
            Some(idx) => match &mut self.children[*idx] {
                Some(child) => {
                    let something_was_deleted = child.delete_prefix(&prefix[1..], exact);
                    if child.is_empty() {
                        self.children[*idx] = None;
                    }
                    something_was_deleted
                }
                None => {
                    if exact {
                        Err(StateError::EntryNotFound)
                    } else {
                        Err(StateError::SubtreeWithPrefixNotFound)
                    }
                }
            },
            None => {
                // If `exact` and we found a non-leaf node, then do nothing and return false.
                if exact && self.data.is_none() {
                    // Make no changes and return false.
                    return Ok(());
                }

                // If not `exact` delete the children, as we are deleting the whole prefix.
                if !exact {
                    self.children.iter_mut().for_each(|child| {
                        *child = None;
                    });
                }

                self.data = None;
                Ok(())
            }
        }
    }

    // A node is considered empty when it has no data and no children.
    fn is_empty(&self) -> bool { self.data.is_none() && self.children.iter().all(|x| x.is_none()) }
}

#[cfg(test)]
mod tests {
    use crate::test_infrastructure::{trie::StateTrie, TestStateEntry};
    use concordium_contracts_common::{to_bytes, Deserial, Read, Seek, SeekFrom, Write};

    /// Create an entry and unwrap the result.
    fn create_entry(trie: &mut StateTrie, key: &[u8]) -> TestStateEntry {
        trie.create_entry(key).expect("Failed to create entry")
    }

    /// Delete an entry and unwrap the result.
    fn delete_entry(trie: &mut StateTrie, entry: TestStateEntry) {
        trie.delete_entry(entry).expect("Failed to delete entry")
    }

    #[test]
    fn insert_get_test() {
        let expected_value = "hello";
        let key = [0, 1, 2];
        let mut trie = StateTrie::new();

        create_entry(&mut trie, &key)
            .write_all(&to_bytes(&expected_value))
            .expect("Writing to state failed.");

        let mut entry = trie.lookup(&key).expect("Entry not found");
        let actual_value = String::deserial(&mut entry).unwrap();
        assert_eq!(&expected_value, &actual_value);
    }

    #[test]
    fn delete_entry_test() {
        let key1 = [0];
        let key2 = [0, 0]; // A leaf, which is the child of the key1 node.
        let mut trie = StateTrie::new();
        create_entry(&mut trie, &key1);
        create_entry(&mut trie, &key2);

        // Both entries exist in the tree.
        let entry1 = trie.lookup(&key1).expect("entry1 not found");
        assert!(trie.lookup(&key2).is_some());

        delete_entry(&mut trie, entry1); // Delete the data in the parent node.
        assert!(trie.lookup(&key1).is_none());
        assert!(trie.lookup(&key2).is_some()); // The child should still exist.
    }

    #[test]
    fn delete_prefix_test() {
        let key1 = [0];
        let key2 = [0, 0];
        let key3 = [0, 0, 0];

        let mut trie = StateTrie::new();
        create_entry(&mut trie, &key1);
        create_entry(&mut trie, &key2);
        create_entry(&mut trie, &key3);

        assert!(trie.delete_prefix(&key2).is_ok());

        assert!(trie.lookup(&key1).is_some());
        assert!(trie.lookup(&key2).is_none());
        assert!(trie.lookup(&key3).is_none());
    }

    #[test]
    fn double_create_overwrites_data() {
        let key = [];
        let mut trie = StateTrie::new();
        create_entry(&mut trie, &key)
            .write_all(&to_bytes(&"hello"))
            .expect("Writing to state failed");

        // Creating again overwrites the old data.
        let res = String::deserial(&mut create_entry(&mut trie, &key));

        assert!(res.is_err())
    }

    #[test]
    fn iterator_test() {
        let mut trie = StateTrie::new();

        create_entry(&mut trie, b"a").write_u8(42).unwrap();
        create_entry(&mut trie, b"ab").write_u8(43).unwrap();
        let mut entry_abd = create_entry(&mut trie, b"abd");
        let mut entry_abdf = create_entry(&mut trie, b"abdf");
        let mut entry_abdg = create_entry(&mut trie, b"abdg");
        let mut entry_abe = create_entry(&mut trie, b"abe");
        create_entry(&mut trie, b"ac").write_u8(44).unwrap();

        entry_abd.write_u8(0).unwrap();
        entry_abdf.write_u8(1).unwrap();
        entry_abdg.write_u8(2).unwrap();
        entry_abe.write_u8(3).unwrap();

        // Get an iterator of the trie.
        let mut iter = trie.iterator(b"ab").unwrap();
        assert_eq!(u8::deserial(&mut iter.next().unwrap()), Ok(0));
        assert_eq!(u8::deserial(&mut iter.next().unwrap()), Ok(1));
        assert_eq!(u8::deserial(&mut iter.next().unwrap()), Ok(2));
        assert_eq!(u8::deserial(&mut iter.next().unwrap()), Ok(3));
        assert!(iter.next().is_none());

        // Delete some entries.
        trie.delete_iterator(iter);
        assert!(trie.delete_entry(entry_abd).is_ok());
        delete_entry(&mut trie, entry_abdf);
        delete_entry(&mut trie, entry_abe);

        // Only "abdg" is left.
        let mut new_trie = trie.iterator(b"ab").unwrap();
        assert_eq!(u8::deserial(&mut new_trie.next().unwrap()), Ok(2));
        assert!(new_trie.next().is_none());
    }

    #[test]
    fn index_conversion() {
        let expected_key1 = [1, 2, 3, 4, 5, 6, 7];
        let expected_key2 = [92, 255, 23, 5];
        let index1 = super::to_indexes(&expected_key1);
        let index2 = super::to_indexes(&expected_key2);
        let actual_key1 = super::from_indexes(&index1);
        let actual_key2 = super::from_indexes(&index2);
        assert_eq!(expected_key1, &actual_key1[..]);
        assert_eq!(expected_key2, &actual_key2[..]);
    }

    #[test]
    fn write_to_deleted_entry_should_fail() {
        let mut trie = StateTrie::new();
        let mut entry = create_entry(&mut trie, b"ab");
        assert!(entry.write_u8(1).is_ok());
        trie.delete_prefix(&[]).unwrap();
        assert!(entry.write_u8(1).is_err());
    }

    #[test]
    fn seek_on_deleted_entry_should_fail() {
        let mut trie = StateTrie::new();
        let mut entry = create_entry(&mut trie, b"ab");
        assert!(entry.write_u8(1).is_ok());
        trie.delete_prefix(&[]).unwrap();
        assert!(entry.seek(SeekFrom::Start(0)).is_err());
    }

    #[test]
    fn read_from_deleted_entry_should_fail() {
        let mut trie = StateTrie::new();
        let mut entry = create_entry(&mut trie, b"ab");
        assert!(entry.write_u8(1).is_ok());
        trie.delete_prefix(&[]).unwrap();
        // Manually reset offset, since Seek will also fail.
        entry.cursor.offset = 0;
        assert!(entry.read_u8().is_err());
    }

    #[test]
    fn read_from_deleted_aliased_entry_should_fail() {
        let mut trie = StateTrie::new();
        let mut entry = create_entry(&mut trie, b"ab");
        let mut alias_entry = create_entry(&mut trie, b"ab");
        assert!(entry.write_u8(1).is_ok());
        trie.delete_prefix(&[]).unwrap();
        assert!(alias_entry.read_u8().is_err());
    }
}
