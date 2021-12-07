use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    rc::Rc,
};

use crate::StateEntryId;

use super::StateEntryTest;

const BRANCHING_FACTOR: usize = 4;

#[derive(PartialEq, Eq)]
enum Index {
    Zero,
    One,
    Two,
    Three,
}

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

    fn to_indexes(key: &[u8]) -> Vec<Index> {
        // Expects input to be in range 0..4.
        // Will panic if that is not the case.
        fn to_index(x: u8) -> Index {
            match x {
                0 => Index::Zero,
                1 => Index::One,
                2 => Index::Two,
                3 => Index::Three,
                invalid => panic!("Input should be in range 0..4, but got {}.", invalid),
            }
        }

        let mut indexes = Vec::new();
        for byte in key {
            indexes.push(to_index((byte & 0b_11_00_00_00) >> 6));
            indexes.push(to_index((byte & 0b_00_11_00_00) >> 4));
            indexes.push(to_index((byte & 0b_00_00_11_00) >> 2));
            indexes.push(to_index(byte & 0b_00_00_00_11));
        }
        indexes
    }
}

struct Node {
    entry:    Option<Rc<RefCell<Vec<u8>>>>,
    children: [Option<Box<Node>>; BRANCHING_FACTOR],
}

impl std::ops::Index<&Index> for [Option<Box<Node>>] {
    type Output = Option<Box<Node>>;

    fn index(&self, index: &Index) -> &Self::Output {
        match index {
            Index::Zero => &self[0],
            Index::One => &self[1],
            Index::Two => &self[2],
            Index::Three => &self[3],
        }
    }
}

impl std::ops::IndexMut<&Index> for [Option<Box<Node>>] {
    fn index_mut(&mut self, index: &Index) -> &mut Self::Output {
        match index {
            Index::Zero => &mut self[0],
            Index::One => &mut self[1],
            Index::Two => &mut self[2],
            Index::Three => &mut self[3],
        }
    }
}

impl Node {
    pub fn new() -> Self {
        Self {
            entry:    None,
            children: Default::default(),
        }
    }

    fn lookup(&self, indexes: &[Index]) -> Option<Rc<RefCell<Vec<u8>>>> {
        match indexes.first() {
            Some(idx) => self.children[idx].as_ref().and_then(|node| node.lookup(&indexes[1..])),
            None => match &self.entry {
                Some(entry) => Some(Rc::clone(&entry)),
                None => None,
            },
        }
    }

    fn create(&mut self, indexes: &[Index]) -> Rc<RefCell<Vec<u8>>> {
        match indexes.first() {
            Some(idx) => {
                self.children[idx].get_or_insert(Box::new(Self::new())).create(&indexes[1..])
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
            Some(idx) => match &mut self.children[idx] {
                Some(child) => {
                    let something_was_deleted = child.delete_prefix(&prefix[1..], exact);
                    if child.is_empty() {
                        self.children[idx] = None;
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

    // A node is considered empty when it has no data and no children.
    fn is_empty(&self) -> bool { self.entry.is_none() && self.children.iter().all(|x| x.is_none()) }
}

#[cfg(test)]
mod tests {
    use concordium_contracts_common::{to_bytes, Deserial, Write};

    use crate::test_infrastructure::trie::StateTrie;

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
}
