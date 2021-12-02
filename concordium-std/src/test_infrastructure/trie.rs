use std::{cell::RefCell, rc::Rc};

use crate::StateEntryId;

#[derive(PartialEq, Eq)]
enum Index {
    Zero,
    One,
    Two,
    Three,
}

pub struct StateTrie {
    value: Option<Rc<RefCell<Vec<u8>>>>,

    child_zero:  Option<Box<StateTrie>>,
    child_one:   Option<Box<StateTrie>>,
    child_two:   Option<Box<StateTrie>>,
    child_three: Option<Box<StateTrie>>,
}

impl StateTrie {
    pub fn new() -> Self {
        Self {
            value:       None,
            child_zero:  None,
            child_one:   None,
            child_two:   None,
            child_three: None,
        }
    }

    pub fn lookup(&self, key: &[u8]) -> Option<Rc<RefCell<Vec<u8>>>> {
        let indexes = StateTrie::to_indexes(key);
        self.lookup_aux(&indexes)
    }

    fn lookup_aux(&self, indexes: &[Index]) -> Option<Rc<RefCell<Vec<u8>>>> {
        match indexes.first() {
            Some(idx) => match idx {
                Index::Zero => {
                    self.child_zero.as_ref().and_then(|trie| trie.lookup_aux(&indexes[1..]))
                }
                Index::One => {
                    self.child_one.as_ref().and_then(|trie| trie.lookup_aux(&indexes[1..]))
                }
                Index::Two => {
                    self.child_two.as_ref().and_then(|trie| trie.lookup_aux(&indexes[1..]))
                }
                Index::Three => {
                    self.child_three.as_ref().and_then(|trie| trie.lookup_aux(&indexes[1..]))
                }
            },
            None => match &self.value {
                Some(val) => Some(Rc::clone(&val)),
                None => None,
            },
        }
    }

    pub fn create(&mut self, key: &[u8]) -> Rc<RefCell<Vec<u8>>> {
        let indexes = StateTrie::to_indexes(key);
        self.create_aux(&indexes)
    }

    fn create_aux(&mut self, indexes: &[Index]) -> Rc<RefCell<Vec<u8>>> {
        match indexes.first() {
            Some(idx) => match idx {
                Index::Zero => self
                    .child_zero
                    .get_or_insert(Box::new(StateTrie::new()))
                    .create_aux(&indexes[1..]),
                Index::One => self
                    .child_one
                    .get_or_insert(Box::new(StateTrie::new()))
                    .create_aux(&indexes[1..]),
                Index::Two => self
                    .child_two
                    .get_or_insert(Box::new(StateTrie::new()))
                    .create_aux(&indexes[1..]),
                Index::Three => self
                    .child_three
                    .get_or_insert(Box::new(StateTrie::new()))
                    .create_aux(&indexes[1..]),
            },
            None => {
                let new_value = Rc::new(RefCell::new(Vec::new()));
                let new_value_clone = Rc::clone(&new_value);
                self.value = Some(new_value);
                new_value_clone
            }
        }
    }

    pub fn delete_entry(&mut self, entry_id: StateEntryId) -> bool { todo!() }

    pub fn delete_prefix(&mut self, prefix: &[u8], exact: bool) -> bool { todo!() }

    fn to_indexes(key: &[u8]) -> Vec<Index> {
        let mut indexes = Vec::new();
        for byte in key {
            indexes.push(StateTrie::to_index((byte & 0b_11_00_00_00) >> 6));
            indexes.push(StateTrie::to_index((byte & 0b_00_11_00_00) >> 4));
            indexes.push(StateTrie::to_index((byte & 0b_00_00_11_00) >> 2));
            indexes.push(StateTrie::to_index(byte & 0b_00_00_00_11));
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

#[cfg(test)]
mod tests {
    use concordium_contracts_common::Write;

    use crate::test_infrastructure::trie::StateTrie;

    #[test]
    fn trie_insert_get() {
        let expected_value = vec![9, 8, 7];
        let key = [0, 1, 2];
        let mut trie = StateTrie::new();

        {
            trie.create(&key)
                .as_ref()
                .borrow_mut()
                .write_all(&expected_value)
                .expect("Writing to state failed.");
        }

        let entry = trie.lookup(&key).expect("Entry not found");
        let actual_value: &[u8] = &entry.as_ref().borrow();
        assert_eq!(&expected_value, actual_value);
    }
}
