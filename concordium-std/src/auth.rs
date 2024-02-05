use crate::{self as concordium_std, HasStateApi, StateBuilder, StateMap};
use concordium_contracts_common::Address;

#[derive(Debug, Copy, Clone, concordium_std::Serialize)]
#[repr(transparent)]
/// A set of roles. At most 32 different roles are possible.
pub struct RoleSet {
    inner: u32,
}

pub const ROLE_0: RoleSet = RoleSet {
    inner: 0b1,
};
pub const ROLE_1: RoleSet = RoleSet {
    inner: 0b10,
};
pub const ROLE_2: RoleSet = RoleSet {
    inner: 0b100,
};
pub const ROLE_3: RoleSet = RoleSet {
    inner: 0b1000,
};
pub const ROLE_4: RoleSet = RoleSet {
    inner: 0b10000,
};
pub const ROLE_5: RoleSet = RoleSet {
    inner: 0b100000,
};
pub const ROLE_6: RoleSet = RoleSet {
    inner: 0b1000000,
};
pub const ROLE_7: RoleSet = RoleSet {
    inner: 0b10000000,
};

impl RoleSet {
    pub fn or(self, other: Self) -> Self {
        Self {
            inner: self.inner | other.inner,
        }
    }

    /// Attempt to construct the `n`'th role. Returns `None` if the role
    /// is larger than 32.
    pub fn nth(role: u8) -> Option<Self> {
        Some(Self {
            inner: 1u32.checked_shl(role.into())?,
        })
    }
}

pub struct Roles<S> {
    roles: StateMap<Address, u32, S>,
}

impl<S: HasStateApi> Roles<S> {
    pub fn new(s: &mut StateBuilder<S>) -> Self {
        Self {
            roles: s.new_map(),
        }
    }

    pub fn construct(
        s: &mut StateBuilder<S>,
        values: impl IntoIterator<Item = (Address, RoleSet)>,
    ) -> Self {
        let mut new = Self::new(s);
        for (addr, r) in values {
            new.add(addr, r);
        }
        new
    }

    /// Add a new role for the given address.
    pub fn add(&mut self, address: impl Into<Address>, role_set: RoleSet) {
        let mut entry = self.roles.entry(address.into()).or_insert(0);
        *entry |= role_set.inner;
    }

    /// Remove the set of roles for the given address.
    pub fn remove(&mut self, address: &Address, role: RoleSet) {
        if let Some(mut entry) = self.roles.get_mut(address) {
            *entry &= !role.inner;
        }
    }

    #[must_use]
    /// Check that the address has all the roles specified in the `role_set`.
    pub fn has_all_roles(&self, address: &Address, role_set: RoleSet) -> bool {
        match self.roles.get(&address) {
            Some(roles) => *roles & role_set.inner == role_set.inner,
            None => false,
        }
    }

    #[must_use]
    /// Check that the address has any of the roles specified in the `role_set`.
    pub fn has_any_roles(&self, address: &Address, role_set: RoleSet) -> bool {
        match self.roles.get(&address) {
            Some(roles) => *roles & role_set.inner != 0,
            None => false,
        }
    }

    /// Return roles that are assigned to the given address.
    pub fn roles(&self, address: &Address) -> impl Iterator<Item = RoleSet> {
        struct RoleIterator {
            value: u32,
            pos:   u8,
        }
        impl Iterator for RoleIterator {
            type Item = RoleSet;

            fn next(&mut self) -> Option<Self::Item> {
                while self.pos > 0 {
                    self.pos -= 1;
                    let role = 1u32 << self.pos;
                    if self.value & role != 0 {
                        return Some(RoleSet {
                            inner: role,
                        });
                    }
                }
                None
            }
        }
        if let Some(value) = self.roles.get(address) {
            RoleIterator {
                value: *value,
                pos:   32,
            }
        } else {
            RoleIterator {
                value: 0,
                pos:   0,
            }
        }
    }
}
