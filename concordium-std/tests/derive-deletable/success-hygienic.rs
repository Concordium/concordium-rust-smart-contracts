//! Ensures that `derive(Deletable)` would compile properly without importing any symbols
pub trait ProxyTrait {
    type State: concordium_std::HasStateApi;
}

#[derive(concordium_std::Deletable)]
#[concordium(state_parameter = "T::State")]
pub struct TestDeletableOuter<T: ProxyTrait> {
    pub test_map: concordium_std::StateMap<u32, String, T::State>,
    pub inner: TestDeletableInner<T::State>,
}

#[derive(concordium_std::Deletable)]
#[concordium(state_parameter = "S")]
pub struct TestDeletableInner<S: concordium_std::HasStateApi> {
    pub test_set: concordium_std::StateSet<u64, S>,
}

fn main() {}
