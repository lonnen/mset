# mset

[![CI status](https://github.com/lonnen/mset/actions/workflows/rust.yml/badge.svg)](https://github.com/lonnen/mset/actions/workflows/rust.yml)

This crate provides a [multiset](https://en.wikipedia.org/wiki/Multiset) implementation for rust.

## Overview

A mset, multiset, or bag is a set that allows multiple occurances of an element. It supports many basic set operations, e.g. membership test, union, intersection, and difference.

* [Documentation](https://docs.rs/mset/0.0.1/mset/struct.MultiSet.html)
* [Release Notes](https://github.com/lonnen/mset/releases)

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
mset = "0.1.0"
```

Now, you can use  mset:

```rust
extern crate mset;
```

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.