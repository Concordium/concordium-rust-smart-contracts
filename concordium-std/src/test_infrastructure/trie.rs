use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, VecDeque},
    rc::Rc,
};

use crate::StateEntryId;

use super::StateEntryTest;

const BRANCHING_FACTOR: usize = 4;

type Index = usize;

#[derive(Debug)]
pub struct StateTrie {
    nodes:         Node,
    next_entry_id: Cell<StateEntryId>,
    entry_map:     RefCell<HashMap<StateEntryId, Vec<Index>>>,
}

impl StateTrie {
    pub fn new() -> Self {
        Self {
            nodes:         Node::new(),
            next_entry_id: Cell::new(0),
            entry_map:     RefCell::new(HashMap::new()),
        }
    }

    pub fn lookup(&self, key: &[u8]) -> Option<StateEntryTest> {
        let indexes = Self::to_indexes(key);
        match self.nodes.lookup(&indexes) {
            Some(data) => Some(self.construct_state_entry_test(indexes, data)),
            None => None,
        }
    }

    // Construct a `StateEntryTest` and use interior mutation to add increment
    // next_entry_id and add the entry to the entry_map.
    fn construct_state_entry_test(
        &self,
        indexes: Vec<Index>,
        data: Rc<RefCell<Vec<u8>>>,
    ) -> StateEntryTest {
        // Get the current next_entry_id
        let state_entry_id: u32 = self.next_entry_id.get();

        // Add the id and indexes to the map and increment the next_entry_id
        self.entry_map.borrow_mut().insert(state_entry_id, indexes);
        self.next_entry_id.set(state_entry_id + 1);

        StateEntryTest::new(data, state_entry_id)
    }

    pub fn create(&mut self, key: &[u8]) -> StateEntryTest {
        let indexes = Self::to_indexes(key);
        let data = self.nodes.create(&indexes);
        self.construct_state_entry_test(indexes, data)
    }

    pub fn delete_entry(&mut self, entry: StateEntryTest) -> bool {
        match self.entry_map.borrow_mut().remove(&entry.state_entry_id) {
            Some(indexes) => self.nodes.delete_entry(&indexes),
            None => false, /* Entry did not exist. Only happens when entry was deleted using
                            * delete_prefix. */
        }
    }

    pub fn delete_prefix(&mut self, prefix: &[u8], exact: bool) -> bool {
        self.nodes.delete_prefix(&Self::to_indexes(prefix), exact)
    }

    pub fn iter(&self, prefix: &[u8]) -> Iter { Iter::new(&self, prefix) }

    fn to_indexes(key: &[u8]) -> Vec<Index> {
        let mut indexes = Vec::new();
        for byte in key {
            indexes.push(((byte & 0b_11_00_00_00) >> 6) as Index);
            indexes.push(((byte & 0b_00_11_00_00) >> 4) as Index);
            indexes.push(((byte & 0b_00_00_11_00) >> 2) as Index);
            indexes.push((byte & 0b_00_00_00_11) as Index);
        }
        indexes
    }
}

#[derive(Debug)]
pub struct Iter<'a> {
    node_iter: Option<NodeIter>,
    trie:      &'a StateTrie,
}

impl<'a> Iter<'a> {
    fn new(trie: &'a StateTrie, prefix: &[u8]) -> Self {
        let index_prefix = StateTrie::to_indexes(prefix);
        Self {
            node_iter: trie.nodes.iter(&index_prefix),
            trie,
        }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = StateEntryTest;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.node_iter {
            Some(ref mut node_iter) => node_iter.next().and_then(|(indexes, data)| {
                Some(self.trie.construct_state_entry_test(indexes, data))
            }),
            None => None,
        }
    }
}

#[derive(Debug)]
struct Node {
    entry:    Option<Rc<RefCell<Vec<u8>>>>,
    children: [Option<Box<Node>>; BRANCHING_FACTOR],
}

impl Node {
    fn new() -> Self {
        Self {
            entry:    None,
            children: Default::default(),
        }
    }

    /// Tries to find the data in a node with the given index.
    /// Returns `None` iff the node doesn't exist, or, if the node exists, but
    /// has not data.
    fn lookup(&self, indexes: &[Index]) -> Option<Rc<RefCell<Vec<u8>>>> {
        self.lookup_node(indexes).and_then(|node| match &node.entry {
            Some(entry) => Some(Rc::clone(&entry)),
            None => None,
        })
    }

    /// Tries to find the node with the given index.
    /// Returns `None` if the node doesn't exist.
    fn lookup_node(&self, indexes: &[Index]) -> Option<&Self> {
        match indexes.first() {
            Some(idx) => {
                self.children[*idx].as_ref().and_then(|node| node.lookup_node(&indexes[1..]))
            }
            None => Some(&self),
        }
    }

    fn create(&mut self, indexes: &[Index]) -> Rc<RefCell<Vec<u8>>> {
        match indexes.first() {
            Some(idx) => {
                self.children[*idx].get_or_insert(Box::new(Self::new())).create(&indexes[1..])
            }
            None => {
                let new_entry = Rc::new(RefCell::new(Vec::new()));
                let new_entry_clone = Rc::clone(&new_entry);
                self.entry = Some(new_entry);
                new_entry_clone
            }
        }
    }

    fn delete_entry(&mut self, indexes: &[Index]) -> bool { self.delete_prefix(indexes, true) }

    fn delete_prefix(&mut self, prefix: &[Index], exact: bool) -> bool {
        match prefix.first() {
            Some(idx) => match &mut self.children[*idx] {
                Some(child) => {
                    let something_was_deleted = child.delete_prefix(&prefix[1..], exact);
                    if child.is_empty() {
                        self.children[*idx] = None;
                    }
                    something_was_deleted
                }
                None => false, // No such prefix or entry exists.
            },
            None => {
                // If `exact` and we found a non-leaf node, then do nothing and return false.
                if exact && self.entry.is_none() {
                    // Make no changes and return false.
                    return false;
                }

                // If not `exact` delete the children, as we are deleting the whole prefix.
                if !exact {
                    self.children.iter_mut().for_each(|child| {
                        *child = None;
                    });
                }

                self.entry = None;
                true
            }
        }
    }

    fn iter(&self, prefix: &[Index]) -> Option<NodeIter> {
        self.lookup_node(prefix)
            .and_then(|iter_root_node| Some(NodeIter::new(prefix, iter_root_node)))
    }

    // A node is considered empty when it has no data and no children.
    fn is_empty(&self) -> bool { self.entry.is_none() && self.children.iter().all(|x| x.is_none()) }
}

#[derive(Debug)]
struct NodeIter {
    queue: VecDeque<(Vec<Index>, Rc<RefCell<Vec<u8>>>)>,
}

impl NodeIter {
    fn new(root_index: &[Index], root_of_iter: &Node) -> Self {
        let mut queue = VecDeque::new();

        fn build_queue(
            queue: &mut VecDeque<(Vec<Index>, Rc<RefCell<Vec<u8>>>)>,
            indexes: &mut Vec<Index>,
            node: &Node,
        ) {
            for idx in 0..4 {
                if let Some(child) = &node.children[idx] {
                    // Push current index.
                    indexes.push(idx);

                    if let Some(entry) = &child.entry {
                        queue.push_back((indexes.clone(), Rc::clone(entry)));
                    }
                    build_queue(queue, indexes, &child);

                    // Pop current index again.
                    indexes.pop();
                }
            }
        }

        build_queue(&mut queue, &mut root_index.to_vec(), root_of_iter);

        Self {
            queue,
        }
    }
}

impl Iterator for NodeIter {
    type Item = (Vec<Index>, Rc<RefCell<Vec<u8>>>);

    fn next(&mut self) -> Option<Self::Item> { self.queue.pop_front() }
}

#[cfg(test)]
mod tests {
    use concordium_contracts_common::{to_bytes, Deserial, Write};

    use crate::{test_infrastructure::trie::StateTrie, UnwrapAbort};

    #[test]
    fn insert_get_test() {
        let expected_value = "hello";
        let key = [0, 1, 2];
        let mut trie = StateTrie::new();

        trie.create(&key).write_all(&to_bytes(&expected_value)).expect("Writing to state failed.");

        let mut entry = trie.lookup(&key).expect("Entry not found");
        let actual_value = String::deserial(&mut entry).unwrap();
        assert_eq!(&expected_value, &actual_value);
    }

    #[test]
    fn delete_entry_test() {
        let key1 = [0];
        let key2 = [0, 0]; // A leaf, which is the child of the key1 node.
        let mut trie = StateTrie::new();
        trie.create(&key1);
        trie.create(&key2);

        // Both entries exist in the tree.
        let entry1 = trie.lookup(&key1).expect("entry1 not found");
        assert!(trie.lookup(&key2).is_some());

        trie.delete_entry(entry1); // Delete the data in the parent node.
        assert!(trie.lookup(&key1).is_none());
        assert!(trie.lookup(&key2).is_some()); // The child should still exist.
    }

    #[test]
    fn delete_prefix_test() {
        let key1 = [0];
        let key2 = [0, 0];
        let key3 = [0, 0, 0];

        let mut trie = StateTrie::new();
        trie.create(&key1);
        trie.create(&key2);
        trie.create(&key3);

        assert_eq!(trie.delete_prefix(&key2, false), true);

        assert!(trie.lookup(&key1).is_some());
        assert!(trie.lookup(&key2).is_none());
        assert!(trie.lookup(&key3).is_none());
    }

    #[test]
    fn double_create_overwrites_data() {
        let key = [];
        let mut trie = StateTrie::new();
        trie.create(&key).write_all(&to_bytes(&"hello")).expect("Writing to state failed");

        // Creating again overwrites the old data.
        let res = String::deserial(&mut trie.create(&key));

        assert!(res.is_err())
    }

    #[test]
    fn iterator_test() {
        let mut trie = StateTrie::new();

        trie.create(b"a").write_u8(42).unwrap_abort();
        trie.create(b"ab").write_u8(43).unwrap_abort();
        let mut entry_abd = trie.create(b"abd");
        let mut entry_abdf = trie.create(b"abdf");
        let mut entry_abdg = trie.create(b"abdg");
        let mut entry_abe = trie.create(b"abe");
        trie.create(b"ac").write_u8(44).unwrap_abort();

        entry_abd.write_u8(0).unwrap_abort();
        entry_abdf.write_u8(1).unwrap_abort();
        entry_abdg.write_u8(2).unwrap_abort();
        entry_abe.write_u8(3).unwrap_abort();

        // Get an iterator of the trie.
        let mut iter = trie.iter(b"ab");
        assert_eq!(u8::deserial(&mut iter.next().unwrap_abort()), Ok(0));
        assert_eq!(u8::deserial(&mut iter.next().unwrap_abort()), Ok(1));
        assert_eq!(u8::deserial(&mut iter.next().unwrap_abort()), Ok(2));
        assert_eq!(u8::deserial(&mut iter.next().unwrap_abort()), Ok(3));
        assert_eq!(iter.next(), None);

        // Delete some entries.
        trie.delete_entry(entry_abd);
        trie.delete_entry(entry_abdf);
        trie.delete_entry(entry_abe);

        // Only "abdg" is left.
        let mut new_trie = trie.iter(b"ab");
        assert_eq!(u8::deserial(&mut new_trie.next().unwrap_abort()), Ok(2));
        assert_eq!(new_trie.next(), None);
    }
}
