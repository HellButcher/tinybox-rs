# `tinybox`

<!--
[![Crates.io](https://img.shields.io/crates/v/tinybox.svg?label=tinybox)](https://crates.io/crates/tinybox)
[![docs.rs](https://docs.rs/tinybox/badge.svg)](https://docs.rs/tinybox/)
-->
[![license: MIT/Apache-2.0](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](#license)
[![Rust CI](https://github.com/HellButcher/tinybox/actions/workflows/rust.yml/badge.svg)](https://github.com/HellButcher/tinybox/actions/workflows/rust.yml)

<!-- Short Introduction -->
`TinyBox` is like `Box`, but with an optimization that avoids allocations for small data-structures. This works by storing the value-bits inside the box itself, when the data-structure fits inside a pointer. This is especially usefull for dyn-Traits.

## Example

This example stores a value inside the `TinyBox` without requireing an allocation.
```rust
use tinybox::TinyBox;
let boxed = TinyBox::new(1234usize);
assert_eq!(1234, *boxed)
```

This looks not very usefull, because the value can be stored inside a `usize` variable without `TinyBox`. Here is an more useful example that uses dyn-traits. The `tinybox!` macro is used to coerce the value to a dyn-trait in stable-rust.
```rust
use std::any::{Any,TypeId};
use tinybox::{tinybox, TinyBox};
let boxed = tinybox!(dyn Any = 1234usize);
assert_eq!(TypeId::of::<usize>(), (*boxed).type_id());
assert_eq!(1234, *boxed.downcast::<usize>().unwrap());
```


## `no_std`

This crate should also work without `std`. No additional configuration required.

## License

[license]: #license

This repository is licensed under either of

* MIT license ([LICENSE-MIT] or <http://opensource.org/licenses/MIT>)
* Apache License, Version 2.0, ([LICENSE-APACHE] or <http://www.apache.org/licenses/LICENSE-2.0>)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[LICENSE-MIT]: ../../LICENSE-MIT
[LICENSE-APACHE]: ../../LICENSE-APACHE
