//! Ensures that `derive(Deserial)` would compile properly without importing any symbols
#[derive(concordium_std::Deserial)]
pub struct InnerStruct<A> {
    pub num: u32,
    pub a: A,
}

#[derive(concordium_std::Deserial)]
#[concordium(repr(u8))]
pub enum InnerEnum<B> {
    One(u32),
    #[concordium(tag = 200)]
    TwoHundred(B),
    #[concordium(forward = [5, 6])]
    Three(ForwardedEnum),
}

#[derive(concordium_std::Deserial)]
#[concordium(repr(u8))]
pub enum ForwardedEnum {
    #[concordium(tag = 5)]
    Alpha {
        balance: u32,
    },
    #[concordium(tag = 6)]
    Beta(u16),
}

#[derive(concordium_std::Deserial)]
#[concordium(bound(deserial = ""))]
pub struct ZeroSized<A> {
    _phantom: std::marker::PhantomData<A>,
}

#[derive(concordium_std::Deserial)]
pub struct State<A, B> {
    pub inner_struct: InnerStruct<A>,
    pub inner_enum: InnerEnum<B>,
    pub zero: ZeroSized<A>,
    #[concordium(ensure_ordered)]
    pub ordered_map: std::collections::BTreeMap<u32, u32>,
    #[concordium(size_length = 2)]
    pub numbers: Vec<u32>,
}

fn main() {}
