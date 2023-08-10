//! Ensures that `derive(DeserialWithState)` would compile properly without importing any symbols
type Ok = f32;
type Err = f64;
type Default = str;

#[derive(concordium_std::DeserialWithState)]
#[concordium(state_parameter = "S")]
pub struct Deserial0<S: concordium_std::HasStateApi> {
    pub test_map: concordium_std::StateMap<u32, String, S>,
}

#[derive(concordium_std::DeserialWithState)]
#[concordium(state_parameter = "T")]
struct Deserial1<T, A> {
    map:   concordium_std::StateMap<u32, String, T>,
    other: A,
}

trait ProxyTrait {
    type State: concordium_std::HasStateApi;
}

#[derive(concordium_std::DeserialWithState)]
#[concordium(state_parameter = "T::State")]
struct Deserial2<T: ProxyTrait, A> {
    test_map: concordium_std::StateMap<u32, String, T::State>,
    field:    A,
}

fn main() {}
