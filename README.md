# mset

This crate provides a [multiset](https://en.wikipedia.org/wiki/Multiset) implementation for rust.

## Overview

[![CircleCI](https://circleci.com/gh/lonnen/mset.svg?style=svg)](https://circleci.com/gh/lonnen/mset)
[![Build status](https://ci.appveyor.com/api/projects/status/dv10p89kf73i3kgl?svg=true)](https://ci.appveyor.com/project/lonnen/mset)
[![TravisCI](https://api.travis-ci.com/lonnen/mset.svg?branch=master)](https://travis-ci.com/github/lonnen/mset)

A mset, multiset, or bag is a set that allows multiple occurances of an element. It supports many basic set operations, e.g. membership test, union, intersection, and difference.

* [Documentation](https://docs.rs/mset/0.0.1/mset/struct.MultiSet.html)
* [Release Notes](https://github.com/lonnen/mset/releases)

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
mset = "0.0.4"
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