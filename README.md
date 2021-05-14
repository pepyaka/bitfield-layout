BitField layout
=====
This crate is yet another bitfield handling implementation.

The main goal of this crate - provide binding various data to every bit (flag)
within bitfield layout. In many cases bitfield data are read only and every bit
(flag) has some meaning. Then you getting bitfield data it's useful to get
meaning or/and description of setted flags.

This crate provides basic trait BitFieldLayout that provides convenient methods
for getting flags and it meaning of user defined structures or enums. Also
there is module layouts with accessory structs and macros.

### Documentation

Documentation with examples for the various matching functions and iterators
can be found on the [https://docs.rs/bitfield_layout].

### Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
bitfield_layout = "0.1"
```

### Minimum Rust version policy

This crate's minimum supported `rustc` version is `1.51`.
