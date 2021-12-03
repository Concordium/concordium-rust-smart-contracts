use std::{cell::RefCell, collections::HashMap, ops::AddAssign, rc::Rc};

use crate::StateEntryId;

use super::StateEntryTest;

#[derive(PartialEq, Eq)]
enum Index {
    Zero,
    One,
    Two,
    Three,
}

pub struct StateTrie {
    nodes:         Node,
    next_entry_id: RefCell<StateEntryId>,
    entry_map:     RefCell<HashMap<StateEntryId, Vec<Index>>>,
}

impl StateTrie {
    pub fn new() -> Self {
        Self {
            nodes:         Node::new(),
            next_entry_id: RefCell::new(0),
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
        let state_entry_id: u32 = *self.next_entry_id.borrow();

        // Add the id and indexes to the map and increment the next_entry_id
        self.entry_map.borrow_mut().insert(state_entry_id, indexes);
        self.next_entry_id.borrow_mut().add_assign(1);

        StateEntryTest::new(data, state_entry_id)
    }

    pub fn create(&mut self, key: &[u8]) -> StateEntryTest {
        let indexes = Self::to_indexes(key);
        let data = self.nodes.create(&indexes);
        self.construct_state_entry_test(indexes, data)
    }

    pub fn delete_entry(&mut self, entry: StateEntryTest) -> bool { todo!() }

    pub fn delete_prefix(&mut self, prefix: &[u8], exact: bool) -> bool { todo!() }

    fn to_indexes(key: &[u8]) -> Vec<Index> {
        let mut indexes = Vec::new();
        for byte in key {
            indexes.push(Self::to_index((byte & 0b_11_00_00_00) >> 6));
            indexes.push(Self::to_index((byte & 0b_00_11_00_00) >> 4));
            indexes.push(Self::to_index((byte & 0b_00_00_11_00) >> 2));
            indexes.push(Self::to_index(byte & 0b_00_00_00_11));
        }
        indexes
    }

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
}

struct Node {
    entry:       Option<Rc<RefCell<Vec<u8>>>>,
    child_zero:  Option<Box<Node>>,
    child_one:   Option<Box<Node>>,
    child_two:   Option<Box<Node>>,
    child_three: Option<Box<Node>>,
}

impl Node {
    pub fn new() -> Self {
        Self {
            entry:       None,
            child_zero:  None,
            child_one:   None,
            child_two:   None,
            child_three: None,
        }
    }

    fn lookup(&self, indexes: &[Index]) -> Option<Rc<RefCell<Vec<u8>>>> {
        match indexes.first() {
            Some(idx) => match idx {
                Index::Zero => self.child_zero.as_ref().and_then(|trie| trie.lookup(&indexes[1..])),
                Index::One => self.child_one.as_ref().and_then(|trie| trie.lookup(&indexes[1..])),
                Index::Two => self.child_two.as_ref().and_then(|trie| trie.lookup(&indexes[1..])),
                Index::Three => {
                    self.child_three.as_ref().and_then(|trie| trie.lookup(&indexes[1..]))
                }
            },
            None => match &self.entry {
                Some(entry) => Some(Rc::clone(&entry)),
                None => None,
            },
        }
    }

    fn create(&mut self, indexes: &[Index]) -> Rc<RefCell<Vec<u8>>> {
        match indexes.first() {
            Some(idx) => match idx {
                Index::Zero => {
                    self.child_zero.get_or_insert(Box::new(Self::new())).create(&indexes[1..])
                }
                Index::One => {
                    self.child_one.get_or_insert(Box::new(Self::new())).create(&indexes[1..])
                }
                Index::Two => {
                    self.child_two.get_or_insert(Box::new(Self::new())).create(&indexes[1..])
                }
                Index::Three => {
                    self.child_three.get_or_insert(Box::new(Self::new())).create(&indexes[1..])
                }
            },
            None => {
                let new_entry = Rc::new(RefCell::new(Vec::new()));
                let new_entry_clone = Rc::clone(&new_entry);
                self.entry = Some(new_entry);
                new_entry_clone
            }
        }
    }

    fn delete_entry(&mut self, indexes: &[Index]) -> bool { todo!() }

    // A node is considered empty when it has no data and no children.
    fn is_empty(&self) -> bool {
        self.entry.is_none()
            && self.child_zero.is_none()
            && self.child_one.is_none()
            && self.child_two.is_none()
            && self.child_three.is_none()
    }
}

#[cfg(test)]
mod tests {
    use concordium_contracts_common::{to_bytes, Deserial, Write};

    use crate::test_infrastructure::trie::{Node, StateTrie};

    #[test]
    fn trie_insert_get() {
        let expected_value = "hello";
        let key = [0, 1, 2];
        let mut trie = StateTrie::new();

        trie.create(&key).write_all(&to_bytes(&expected_value)).expect("Writing to state failed.");

        let mut entry = trie.lookup(&key).expect("Entry not found");
        let actual_value = String::deserial(&mut entry).unwrap();
        assert_eq!(&expected_value, &actual_value);
    }

    #[test]
    fn delete_entry() {
        let key = []; // Empty key is root.
        let mut trie = Node::new();
        trie.create(&key);
        let entry = trie.lookup(&key).expect("Entry not found");
        trie.delete_entry(entry);
    }
}
