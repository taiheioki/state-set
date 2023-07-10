# state-set

[![CI](https://github.com/taiheioki/state-set/actions/workflows/ci.yml/badge.svg)](https://github.com/taiheioki/state-set/actions/workflows/ci.yml) ![license](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue)

`state-set` is a Rust crate providing a way to manage a set of states as a bit vector.

## Features

- `StateSet<T>`, a data structure for managing a set of states of a type `T` that implements `State`.
- `State` trait for types that have a finite number of possible states.
- A derive macro for `State` trait to easily implement it for your own types.
- Safe and efficient management of states with compile-time checks.

## Example

```rust
use state_set::*;

#[derive(Debug, State)]
pub enum MyEnum {
    A,
    B,
    C,
    D,
}

let mut set = StateSet::new();
set.insert(MyEnum::A);
set.insert(MyEnum::B);

assert!(set.contains(MyEnum::A));
assert!(!set.contains(MyEnum::C));

for state in set {
    println!("{:?}", state);
}
```

In this example, `MyEnum` is an enumeration with 4 possible states. We use the `#[derive(State)]` macro to automatically implement the `State` trait for `MyEnum`. Then we create a `StateSet` and use it to manage a set of states of `MyEnum`.

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
