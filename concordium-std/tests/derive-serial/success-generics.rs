/// Test ensuring derivation works for types with type parameters.
use concordium_std::*;

#[derive(Serial)]
struct MyStruct<A> {
    field:       A,
    other_field: u8,
}

#[derive(Serial)]
struct MyOtherStruct<A, B> {
    field:       A,
    other_field: B,
}

#[derive(Serial)]
enum MyEnum<A> {
    One(u32),
    Two(A),
}

#[derive(Serial)]
enum MyOtherEnum<A, B> {
    One(u32),
    Two(A, B),
}

fn main() {
    {
        let value = MyStruct::<u32> {
            field:       42,
            other_field: 5,
        };
        let _bytes = to_bytes(&value);
    }
    {
        let value = MyOtherStruct::<u64, u16> {
            field:       42,
            other_field: 5,
        };
        let _bytes = to_bytes(&value);
    }
    {
        let value = MyEnum::<u64>::Two(1);
        let _bytes = to_bytes(&value);
    }
    {
        let value = MyOtherEnum::<u64, u16>::Two(1, 15);
        let _bytes = to_bytes(&value);
    }
}
