//! This crate is yet another bitfield handling implementation.
//! 
//! The main goal of this crate - provide binding for various data to every bit (flag) within bitfield layout.
//! In many cases bitfield data are read-only and every bit (flag) has some meaning.
//! Then you getting bitfield data it's useful to get meaning and/or description of setted flags.
//! 
//! This crate provides basic trait [BitFieldLayout] that provides convenient methods for getting flags
//! and it meanings of user defined structs or enums. Also there is module [layouts] with accessory
//! structs and macros.
//! 
//! # Example: simple string
//! Bits layout within bitfield may be associated with it meaning in many ways. The simple case - each
//! bit (flag) has simple string description.
//! 
//! ```
//! use std::{array, fmt, slice};
//! use either::Either;
//! use bitfield_layout::{Layout, BitFieldLayout};
//! 
//! // New struct that holds bitfield value
//! struct Simple(u8);
//! // Associated bit layout implementation
//! impl Layout for Simple {
//!     type Layout = slice::Iter<'static, &'static str>;
//!     fn layout() -> Self::Layout {
//!         [
//!             "First flag", 
//!             "Second flag", 
//!             "Third flag", 
//!             "Fourth flag", 
//!             "Fifth flag", 
//!             "Sixth flag", 
//!             "Seventh flag", 
//!             "Eighth flag", 
//!         ].iter()
//!     }
//! }
//! // Main trait implementation
//! impl BitFieldLayout for Simple {
//!     type Value = u8;
//!     fn get(&self) -> Self::Value { self.0 }
//!     fn set(&mut self, new: Self::Value) { self.0 = new; }
//! }
//! 
//! // Now we can use methods provided by trait
//! 
//! // Show full data layout (just show flag meanings that we defined)
//! let layout = Simple::layout();
//!
//! let layout_result = layout
//!     .cloned()
//!     .collect::<Vec<_>>();
//! let layout_sample = vec![
//!     "First flag",
//!     "Second flag",
//!     "Third flag",
//!     "Fourth flag",
//!     "Fifth flag",
//!     "Sixth flag",
//!     "Seventh flag",
//!     "Eighth flag",
//! ];
//! assert_eq!(layout_sample, layout_result, "Layout");
//! 
//! // Assign value to aur bitfield type
//! let simple = Simple(0b10101010);
//! // Show every bit (flag) state
//! let bits = simple.bits();
//!
//! let bits_result = bits
//!     .enumerate()
//!     .map(|(n, b)| format!("Bit #{}: {}", n, if b { "Is set" } else { "Not set" }))
//!     .collect::<Vec<_>>();
//! let bits_sample = vec![
//!     "Bit #0: Not set",
//!     "Bit #1: Is set",
//!     "Bit #2: Not set",
//!     "Bit #3: Is set",
//!     "Bit #4: Not set",
//!     "Bit #5: Is set",
//!     "Bit #6: Not set",
//!     "Bit #7: Is set",
//! ];
//! assert_eq!(bits_sample, bits_result, "Bits");
//! 
//! // Show bit (flag) state and it meaning
//! let flags = simple.flags();
//!
//! let flags_result = flags
//!     .map(|f| format!("`{}` is {}", f.value, f.is_set))
//!     .collect::<Vec<_>>();
//! let flags_sample = vec![
//!     "`First flag` is false",
//!     "`Second flag` is true",
//!     "`Third flag` is false",
//!     "`Fourth flag` is true",
//!     "`Fifth flag` is false",
//!     "`Sixth flag` is true",
//!     "`Seventh flag` is false",
//!     "`Eighth flag` is true",
//! ];
//! assert_eq!(flags_sample, flags_result, "Flags");
//! 
//! // Show difference between two bitfield values
//! let other = Simple(0b11001100);
//! let diff = simple.diff(other);
//!
//! let diff_result = diff
//!     .collect::<Vec<_>>();
//! let diff_sample = vec![
//!     Either::Left((1, &"Second flag")),
//!     Either::Right((2, &"Third flag")),
//!     Either::Left((5, &"Sixth flag")),
//!     Either::Right((6, &"Seventh flag")),
//! ];
//! assert_eq!(diff_sample, diff_result, "Diff");
//! ```
//! 
//! # Example: status register of MOS Technology 6502
//! One eight-bit field holds seven pieces of information:
//! 
//! Bit # | Name | Desription
//! ------|------|-----------
//!    0  | Carry flag | Enables numbers larger than a single word to be added/subtracted by carrying a binary digit from a less significant word to the least significant bit of a more significant word as needed.
//!    1  | Zero flag | Indicates that the result of an arithmetic or logical operation (or, sometimes, a load) was zero.
//!    2  | Interrupt flag | Indicates whether interrupts are enabled or masked.
//!    3  | Decimal flag | Indicates that a bit carry was produced between the nibbles as a result of the last arithmetic operation.
//!    4  | Break flag | It can be examined as a value stored on the stack.
//!    5  | Unused | Unused
//!    6  | Overflow flag | Indicates that the signed result of an operation is too large to fit in the register width using two's complement representation.
//!    7  | Negative flag | Indicates that the result of a mathematical operation is negative.
//! 
//! We can handle this register like:
//! ```
//! use std::{array, fmt, slice};
//! use bitfield_layout::{Layout, BitFieldLayout};
//! 
//! // Struct for handle flag name and flag description
//! struct NameAndDescription<'a>(&'a str, &'a str);
//! // Implement Display: Name for basic form "{}" and Description for alternative "{:#}"
//! impl<'a> fmt::Display for NameAndDescription<'a> {
//!     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//!         let s = if f.alternate() { self.1 } else { self.0 };
//!         write!(f, "{}", s)
//!     }
//! }
//! 
//! // New struct that holds bitfield value
//! struct StatusRegister(u8);
//! // Associate bitfield layout with bitfield type
//! impl StatusRegister {
//!     const LAYOUT: [NameAndDescription<'static>; 8] = [
//!         NameAndDescription(
//!             "Carry flag",
//!             "Enables numbers larger than a single word to be added/subtracted by \
//!             carrying a binary digit from a less significant word to the least \
//!             significant bit of a more significant word as needed."
//!         ),
//!         NameAndDescription(
//!             "Zero flag",
//!             "Indicates that the result of an arithmetic or logical operation \
//!             (or, sometimes, a load) was zero."
//!         ),
//!         NameAndDescription(
//!             "Interrupt flag",
//!             "Indicates whether interrupts are enabled or masked."
//!         ),
//!         NameAndDescription(
//!             "Decimal flag",
//!             "Indicates that a bit carry was produced between the nibbles as a \
//!             result of the last arithmetic operation."
//!         ),
//!         NameAndDescription(
//!             "Break flag",
//!             "It can be examined as a value stored on the stack."
//!         ),
//!         NameAndDescription("Unused", "Unused"),
//!         NameAndDescription(
//!             "Overflow flag",
//!             "Indicates that the signed result of an operation is too large to \
//!             fit in the register width using two's complement representation."
//!         ),
//!         NameAndDescription(
//!             "Negative flag",
//!             "Indicates that the result of a mathematical operation is negative."
//!         ),
//!     ];
//! }
//! 
//! // Implement layout iterator
//! impl Layout for StatusRegister {
//!     type Layout = slice::Iter<'static, NameAndDescription<'static>>;
//!     // Take bitfield layout from associated constant
//!     fn layout() -> Self::Layout {
//!         StatusRegister::LAYOUT.iter()
//!     }
//! }
//! // Bitfield trait implementation
//! impl BitFieldLayout for StatusRegister {
//!     type Value = u8;
//!     fn get(&self) -> Self::Value { self.0 }
//!     fn set(&mut self, new: Self::Value) { self.0 = new; }
//! }
//! 
//! // For example our value has setted Interrupt and Negative flags
//! let status = StatusRegister(0b10000100);
//! 
//! let result = status.flags()
//!     .filter(|f| f.is_set)
//!     .map(|f| format!("Name: {}\nDescription: {:#}\n", f.value, f.value))
//!     .collect::<Vec<_>>()
//!     .join("\n");
//! let sample = "\
//! Name: Interrupt flag
//! Description: Indicates whether interrupts are enabled or masked.
//!
//! Name: Negative flag
//! Description: Indicates that the result of a mathematical operation is negative.
//! ";
//! assert_eq!(sample, result);
//! ```
//! 
//! ---
//! There are more examples in [layouts] and [BitField]




#![no_std]

use core::{array, iter, ops};

use either::Either;

#[macro_use]
pub mod layouts;
pub use layouts::*;


/// Main trait for creating bitfield 
///
/// In general you need implement this trait and its dependencies: [Layout]. 
/// This trait already implemented for [BitField].
pub trait BitFieldLayout: Layout {
    type Value: Copy + IntoBits + FromBits;
    /// Returns a copy of the contained value.
    fn get(&self) -> Self::Value;
    /// Sets the contained value.
    fn set(&mut self, new: Self::Value);

    /// Replaces the contained value with val, and returns the old contained value.
    /// ```
    /// # use std::iter;
    /// # use bitfield_layout::{BitFieldLayout, Layout};
    /// # struct Simple(u16);
    /// # impl Layout for Simple {
    /// #     type Layout = iter::Empty<()>;
    /// #     fn layout() -> Self::Layout { iter::empty() }
    /// # }
    /// # impl BitFieldLayout for Simple {
    /// #     type Value = u16;
    /// #     fn get(&self) -> Self::Value { self.0 }
    /// #     fn set(&mut self, new: Self::Value) { self.0 = new; }
    /// # }
    /// let mut simple = Simple(42);
    ///
    /// assert_eq!(42, simple.replace(13));
    /// assert_eq!(13, simple.get());
    /// ```
    fn replace(&mut self, new: Self::Value) -> Self::Value {
        let v = self.get();
        self.set(new);
        v
    }
    /// Swaps the values of two bitfields.
    /// ```
    /// # use std::iter;
    /// # use bitfield_layout::{BitFieldLayout, Layout};
    /// # struct Simple(u16);
    /// # impl Layout for Simple {
    /// #     type Layout = iter::Empty<()>;
    /// #     fn layout() -> Self::Layout { iter::empty() }
    /// # }
    /// # impl BitFieldLayout for Simple {
    /// #     type Value = u16;
    /// #     fn get(&self) -> Self::Value { self.0 }
    /// #     fn set(&mut self, new: Self::Value) { self.0 = new; }
    /// # }
    /// let mut one = Simple(1);
    /// let mut two = Simple(2);
    ///
    /// one.swap(&mut two);
    ///
    /// assert!(one.get() == 2 && two.get() == 1);
    /// ```
    fn swap(&mut self, other: &mut Self) {
        let (a, b) = (self.get(), other.get());
        self.set(b);
        other.set(a);
    }
    /// Updates the contained value using a function and returns the new value.
    /// ```
    /// # use std::iter;
    /// # use bitfield_layout::{BitFieldLayout, Layout};
    /// # struct Simple(u64);
    /// # impl Layout for Simple {
    /// #     type Layout = iter::Empty<()>;
    /// #     fn layout() -> Self::Layout { iter::empty() }
    /// # }
    /// # impl BitFieldLayout for Simple {
    /// #     type Value = u64;
    /// #     fn get(&self) -> Self::Value { self.0 }
    /// #     fn set(&mut self, new: Self::Value) { self.0 = new; }
    /// # }
    /// let mut simple = Simple(1111111111);
    ///
    /// assert_eq!(2222222222, simple.update(|x| x * 2));
    /// assert_eq!(2222222222, simple.get());
    /// ```
    fn update<F>(&mut self, f: F) -> Self::Value
    where
        F: FnOnce(Self::Value) -> Self::Value,
    {
        let v = f(self.get());
        self.set(v);
        self.get()
    }

    /// Set the specified bit (flag) in-place. Returns current state
    /// ```
    /// # use std::iter;
    /// # use bitfield_layout::{BitFieldLayout, Layout};
    /// # struct Simple(u64);
    /// # impl Layout for Simple {
    /// #     type Layout = iter::Empty<()>;
    /// #     fn layout() -> Self::Layout { iter::empty() }
    /// # }
    /// # impl BitFieldLayout for Simple {
    /// #     type Value = u64;
    /// #     fn get(&self) -> Self::Value { self.0 }
    /// #     fn set(&mut self, new: Self::Value) { self.0 = new; }
    /// # }
    /// let mut simple = Simple(0b10011001);
    ///
    /// assert_eq!(false, simple.insert_flag(2, true));
    /// assert_eq!(0b10011101, simple.get());
    /// ```
    fn insert_flag(&mut self, position: usize, b: bool) -> bool {
        let mut result = false;
        let bits = self.get()
            .into_bits()
            .enumerate()
            .map(|(n, is_set)| {
                if n == position {
                    result = is_set;
                    b
                } else {
                    is_set
                }
            });
        self.set(Self::Value::from_bits(bits));
        result
    }
    /// The specified bit (flag) will be inverted
    /// ```
    /// # use std::iter;
    /// # use bitfield_layout::{BitFieldLayout, Layout};
    /// # struct Simple(u64);
    /// # impl Layout for Simple {
    /// #     type Layout = iter::Empty<()>;
    /// #     fn layout() -> Self::Layout { iter::empty() }
    /// # }
    /// # impl BitFieldLayout for Simple {
    /// #     type Value = u64;
    /// #     fn get(&self) -> Self::Value { self.0 }
    /// #     fn set(&mut self, new: Self::Value) { self.0 = new; }
    /// # }
    /// let mut simple = Simple(0b10011001);
    ///
    /// simple.toggle_flag(0);
    ///
    /// assert_eq!(0b10011000, simple.get());
    /// ```
    fn toggle_flag(&mut self, position: usize) {
        let bits = self.get()
            .into_bits()
            .enumerate()
            .map(|(n, is_set)| {
                if n == position {
                    !is_set
                } else {
                    is_set
                }
            });
        self.set(Self::Value::from_bits(bits));
    }
    /// Return iterator through bitfield value bits. Every bit represents as bool value.
    /// ```
    /// # use std::iter;
    /// # use bitfield_layout::{BitFieldLayout, Layout};
    /// # struct Simple(u8);
    /// # impl Layout for Simple {
    /// #     type Layout = iter::Empty<()>;
    /// #     fn layout() -> Self::Layout { iter::empty() }
    /// # }
    /// # impl BitFieldLayout for Simple {
    /// #     type Value = u8;
    /// #     fn get(&self) -> Self::Value { self.0 }
    /// #     fn set(&mut self, new: Self::Value) { self.0 = new; }
    /// # }
    /// let mut simple = Simple(0b01010101);
    ///
    /// assert!(simple.bits().step_by(2).all(|v| v == true));
    /// ```
    fn bits(&self) -> Bits<<Self::Value as IntoBits>::Bytes> {
        self.get().into_bits()
    }
    /// Return iterator through bitfield value flags. Every flag contains bit state (set or unset)
    /// and item (record) value - string in simple case.
    /// ```
    /// # use std::{iter, slice};
    /// # use bitfield_layout::{BitFieldLayout, Flag, Layout};
    /// struct Simple(u8);
    /// impl Layout for Simple {
    ///     type Layout = slice::Iter<'static, &'static str>;
    ///     fn layout() -> Self::Layout {
    ///         [
    ///             "First",
    ///             "Second",
    ///             "Third",
    ///             "Fourth",
    ///             "Fifth",
    ///             "Sixth",
    ///             "Seventh",
    ///             "Eighth",
    ///         ].iter()
    ///     }
    /// }
    /// # impl BitFieldLayout for Simple {
    /// #     type Value = u8;
    /// #     fn get(&self) -> Self::Value { self.0 }
    /// #     fn set(&mut self, new: Self::Value) { self.0 = new; }
    /// # }
    /// let mut simple = Simple(0b01010101);
    ///
    /// assert_eq!(Flag { is_set: true, value: &"First"}, simple.flags().next().unwrap());
    /// ```
    fn flags(&self) -> Flags<Self::Layout, Bits<<Self::Value as IntoBits>::Bytes>> {
        Flags::new(Self::layout(), self.bits())
    }
    /// Helps to find difference between two bitfield values.
    /// ```
    /// # use std::{iter, slice};
    /// # use either::Either;
    /// # use bitfield_layout::{BitFieldLayout, Flag, Layout};
    /// struct Simple(u8);
    /// impl Layout for Simple {
    ///     type Layout = slice::Iter<'static, &'static str>;
    ///     fn layout() -> Self::Layout {
    ///         [
    ///             "First",
    ///             "Second",
    ///             "Third",
    ///             "Fourth",
    ///             "Fifth",
    ///             "Sixth",
    ///             "Seventh",
    ///             "Eighth",
    ///         ].iter()
    ///     }
    /// }
    /// # impl BitFieldLayout for Simple {
    /// #     type Value = u8;
    /// #     fn get(&self) -> Self::Value { self.0 }
    /// #     fn set(&mut self, new: Self::Value) { self.0 = new; }
    /// # }
    /// let mut left =  Simple(0b01010101);
    /// let mut right = Simple(0b01010001);
    ///
    /// assert_eq!(vec![Either::Left((2, &"Third"))], left.diff(right).collect::<Vec<_>>());
    /// ```
    fn diff(&self, other: Self) -> Diff<Self::Layout, Bits<<Self::Value as IntoBits>::Bytes>>
    where
        Self: Sized,
    {
        Diff::new(self.flags(), other.flags())
    }
}

/// Associated bits layout
pub trait Layout {
    /// Layout iterator. Typically constant array or slice
    type Layout: Iterator;
    /// Return iterator through layout items. Actual layout may be implemented inside this
    /// function or be a associated constant of bitfield type
    fn layout() -> Self::Layout;
}


/// Converts value to bit iterator
pub trait IntoBits {
    type Bytes: Iterator<Item = u8>;
    fn into_bits(self) -> Bits<Self::Bytes>;
}
impl IntoBits for u8 {
    type Bytes = array::IntoIter<u8, 1>;
    fn into_bits(self) -> Bits<Self::Bytes> {
        self.to_ne_bytes().into_bits()
    }
}
impl IntoBits for u16 {
    type Bytes = array::IntoIter<u8, 2>;
    fn into_bits(self) -> Bits<Self::Bytes> {
        self.to_ne_bytes().into_bits()
    }
}
impl IntoBits for u32 {
    type Bytes = array::IntoIter<u8, 4>;
    fn into_bits(self) -> Bits<Self::Bytes> {
        self.to_ne_bytes().into_bits()
    }
}
impl IntoBits for u64 {
    type Bytes = array::IntoIter<u8, 8>;
    fn into_bits(self) -> Bits<Self::Bytes> {
        self.to_ne_bytes().into_bits()
    }
}
impl IntoBits for u128 {
    type Bytes = array::IntoIter<u8, 16>;
    fn into_bits(self) -> Bits<Self::Bytes> {
        self.to_ne_bytes().into_bits()
    }
}
impl<const N: usize> IntoBits for [u8; N] {
    type Bytes = array::IntoIter<u8, N>;
    fn into_bits(self) -> Bits<Self::Bytes> {
        Bits::new(array::IntoIter::new(self))
    }
}

// At moment const expression can not contain the generic parameter,
// so we can not just define [u8; { M * N }] array.
// To implement IntoBits for [u16; N], [u32; N], [u64; N] and [u128; N] we will
// use some tricks.
impl<const N: usize> IntoBits for [u16; N] {
    type Bytes = iter::Flatten<array::IntoIter<array::IntoIter<u8, N>, 2>>;
    fn into_bits(self) -> Bits<Self::Bytes> {
        // array::IntoIter has no Copy trait, so we will use copypaste method
        let mut result = [
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
        ];
        let mut buf = [0u8; N];
        let bytes = self.iter()
            .map(|d| array::IntoIter::new(d.to_ne_bytes()))
            .flatten();
        for (n, byte) in bytes.enumerate() {
            let i = n % N;
            buf[i] = byte;
            if i == N - 1 {
                result[n / N] = array::IntoIter::new(buf);
            }
        }
        Bits::new(array::IntoIter::new(result).flatten())
    }
}
impl<const N: usize> IntoBits for [u32; N] {
    type Bytes = iter::Flatten<array::IntoIter<array::IntoIter<u8, N>, 4>>;
    fn into_bits(self) -> Bits<Self::Bytes> {
        // array::IntoIter has no Copy trait, so we will use copypaste method
        let mut result = [
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
        ];
        let mut buf = [0u8; N];
        let bytes = self.iter()
            .map(|d| array::IntoIter::new(d.to_ne_bytes()))
            .flatten();
        for (n, byte) in bytes.enumerate() {
            let i = n % N;
            buf[i] = byte;
            if i == N - 1 {
                result[n / N] = array::IntoIter::new(buf);
            }
        }
        Bits::new(array::IntoIter::new(result).flatten())
    }
}
impl<const N: usize> IntoBits for [u64; N] {
    type Bytes = iter::Flatten<array::IntoIter<array::IntoIter<u8, N>, 8>>;
    fn into_bits(self) -> Bits<Self::Bytes> {
        // array::IntoIter has no Copy trait, so we will use copypaste method
        let mut result = [
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
        ];
        let mut buf = [0u8; N];
        let bytes = self.iter()
            .map(|d| array::IntoIter::new(d.to_ne_bytes()))
            .flatten();
        for (n, byte) in bytes.enumerate() {
            let i = n % N;
            buf[i] = byte;
            if i == N - 1 {
                result[n / N] = array::IntoIter::new(buf);
            }
        }
        Bits::new(array::IntoIter::new(result).flatten())
    }
}
impl<const N: usize> IntoBits for [u128; N] {
    type Bytes = iter::Flatten<array::IntoIter<array::IntoIter<u8, N>, 16>>;
    fn into_bits(self) -> Bits<Self::Bytes> {
        // array::IntoIter has no Copy trait, so we will use copypaste method
        let mut result = [
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
            array::IntoIter::new([0u8; N]),
        ];
        let mut buf = [0u8; N];
        let bytes = self.iter()
            .map(|d| array::IntoIter::new(d.to_ne_bytes()))
            .flatten();
        for (n, byte) in bytes.enumerate() {
            let i = n % N;
            buf[i] = byte;
            if i == N - 1 {
                result[n / N] = array::IntoIter::new(buf);
            }
        }
        Bits::new(array::IntoIter::new(result).flatten())
    }
}

/// Converts bit iterator to value
pub trait FromBits {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self;
}
impl FromBits for u8 {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        u8::from_ne_bytes(<[u8; 1]>::from_bits(bits))
    }
}
impl FromBits for u16 {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        u16::from_ne_bytes(<[u8; 2]>::from_bits(bits))
    }
}
impl FromBits for u32 {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        u32::from_ne_bytes(<[u8; 4]>::from_bits(bits))
    }
}
impl FromBits for u64 {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        u64::from_ne_bytes(<[u8; 8]>::from_bits(bits))
    }
}
impl FromBits for u128 {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        u128::from_ne_bytes(<[u8; 16]>::from_bits(bits))
    }
}
impl<const N: usize> FromBits for [u8; N] {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        let mut result = [0u8; N];
        for (i, is_set) in bits.enumerate().take(N * 8) {
            if is_set {
                result[i / 8] |= 1 << (i % 8)
            }
        }
        result
    }
}
impl<const N: usize> FromBits for [u16; N] {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        <[[u8; 2]; N]>::from_bits(bits).iter()
            .map(|arr| u16::from_ne_bytes(*arr))
            .enumerate()
            .fold([0; N], |mut result, (n, v)| { result[n] = v; result })
    }
}
impl<const N: usize> FromBits for [u32; N] {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        <[[u8; 4]; N]>::from_bits(bits).iter()
            .map(|arr| u32::from_ne_bytes(*arr))
            .enumerate()
            .fold([0; N], |mut result, (n, v)| { result[n] = v; result })
    }
}
impl<const N: usize> FromBits for [u64; N] {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        <[[u8; 8]; N]>::from_bits(bits).iter()
            .map(|arr| u64::from_ne_bytes(*arr))
            .enumerate()
            .fold([0; N], |mut result, (n, v)| { result[n] = v; result })
    }
}
impl<const N: usize> FromBits for [u128; N] {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        <[[u8; 16]; N]>::from_bits(bits).iter()
            .map(|arr| u128::from_ne_bytes(*arr))
            .enumerate()
            .fold([0; N], |mut result, (n, v)| { result[n] = v; result })
    }
}
impl<const N: usize, const M: usize> FromBits for [[u8; N]; M] {
    fn from_bits<I: Iterator<Item = bool>>(bits: I) -> Self {
        let mut result = [[0u8; N]; M];
        for (i, is_set) in bits.enumerate().take(N * M * 8) {
            if is_set {
                let m = (i / 8) % M;
                let n = (i / 8) % N;
                result[m][n] |= 1 << (i % 8)
            }
        }
        result
    }
}

/// An iterator through value bits
#[derive(Debug, Clone, Copy)]
pub struct Bits<I> {
    iter: I,
    byte: u8,
    position: usize
}
impl<I: Iterator<Item = u8>> Bits<I> {
    pub fn new(iter: I) -> Self {
        Self { iter, byte: 0, position: 0 }
    }
}
impl<I: Iterator<Item = u8>> Iterator for Bits<I> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position == 0 {
            self.byte = self.iter.next()?;
        }
        let position = self.position;
        self.position = (self.position + 1) % 8;
        Some(self.byte & (1 << position) != 0)
    }
}

/// Handle flag state and flag meaning
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Flag<T> {
    pub is_set: bool,
    pub value: T,
}

/// An iterator through [Flag]s
#[derive(Debug, Clone)]
pub struct Flags<L, B>
where
    L: Iterator,
    B: Iterator<Item = bool>
{
    layout: L,
    bits: B,
}
impl<L, B> Flags<L, B>
where
    L: Iterator,
    B: Iterator<Item = bool>
{
    pub fn new(layout: L, bits: B) -> Self {
        Self { layout, bits, }
    }
}
impl<L, B> Iterator for Flags<L, B>
where
    L: Iterator,
    B: Iterator<Item = bool>
{
    type Item = Flag<L::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.layout.next()?;
        let is_set = self.bits.next()?;
        Some(Flag { is_set, value })
    }
}

/// An iterator through non equal flags
#[derive(Debug, Clone)]
pub struct Diff<L, B>
where
    L: Iterator,
    B: Iterator<Item = bool>
{
    left: Flags<L, B>,
    right: Flags<L, B>,
    position: usize,
}
impl<L, B> Diff<L, B>
where
    L: Iterator,
    B: Iterator<Item = bool>
{
    fn new(left: Flags<L, B>, right: Flags<L, B>) -> Self {
        Self { left, right, position: 0 }
    }
}
impl<L, T, B> Iterator for Diff<L, B>
where
    L: Iterator<Item = T>,
    B: Iterator<Item = bool>
{
    type Item = Either<(usize, T), (usize, T)>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let left = self.left.next()?;
            let right = self.right.next()?;
            let position = self.position;
            self.position += 1;
            match (left.is_set, right.is_set) {
                (true, false) =>
                    return Some(Either::Left((position, left.value))),
                (false, true) =>
                    return Some(Either::Right((position, right.value))),
                _ => continue,
            }
        }
    }
}

/// Accessory struct for convinient type construction
///
/// This structure holds value of created bitfield type and may be used for types that doesn't has
/// own value field: enums and unit-like structs.
///
/// ## Enum wrapper
/// Using enumeration as bitfield type has the following advantage - you can bind bit (flag) to one of
/// enum variants.
/// ```
/// # use std::{array, fmt, slice};
/// # use bitfield_layout::{BitFieldLayout, BitField, Layout};
/// 
/// // Declare new bitfield type
/// enum EightFlags {
///     One,
///     Two,
///     Three,
///     Four,
///     OemReserved(u8), // Reserved field referenced to multiple bits
///     FutureReserved(u8), // Reserved field referenced to multiple bits
/// }
/// // Implement Dispaly trait for basic and alternative views
/// impl fmt::Display for EightFlags {
///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
///         match (self, f.alternate()) {
///             // Basic view
///             (Self::One,   false) => write!(f, "one"),
///             (Self::Two,   false) => write!(f, "two"),
///             (Self::Three, false) => write!(f, "three"),
///             (Self::Four,  false) => write!(f, "four"),
///             // Alternative view
///             (Self::One,   true)  => write!(f, "ONE"),
///             (Self::Two,   true)  => write!(f, "TWO"),
///             (Self::Three, true)  => write!(f, "THREE"),
///             (Self::Four,  true)  => write!(f, "FOUR"),
///             // Reserved fields
///             (Self::OemReserved(v), _) => write!(f, "OEM reserved (#{})", v),
///             (Self::FutureReserved(v), _) => write!(f, "Reserved for future usage (#{})", v),
///         }
///     }
/// }
/// // Implement constant bit layout for this type
/// impl EightFlags {
///     const LAYOUT: [Self; 8] = [
///         Self::One,
///         Self::Two,
///         Self::Three,
///         Self::Four,
///         Self::OemReserved(4),
///         Self::OemReserved(5),
///         Self::FutureReserved(6),
///         Self::FutureReserved(7),
///     ];
/// }
/// // Implement Layout for enum created early
/// impl Layout for EightFlags {
///     type Layout = std::slice::Iter<'static, EightFlags>;
///     fn layout() -> Self::Layout { EightFlags::LAYOUT.iter() }
/// }
/// 
/// // Now we can use wrapped bitfield enum
/// let bf: BitField<EightFlags, u8> = BitField::new(0b01100101);
/// 
/// // Get only setted flags
/// let result = bf.flags()
///     .filter_map(|f| {
///         if f.is_set {
///             match f.value {
///                 EightFlags::OemReserved(v) =>
///                     Some(format!("Reserved flag #{}", v)),
///                 EightFlags::FutureReserved(_) =>
///                     Some(format!("{}", f.value)),
///                 v @ _ =>
///                     Some(format!("Name: {}, Description: {:#}", v, v)),
///             }
///         } else {
///             None
///         }
///     })
///     .collect::<Vec<_>>();
/// 
/// let sample = vec![
///     "Name: one, Description: ONE",
///     "Name: three, Description: THREE",
///     "Reserved flag #5",
///     "Reserved for future usage (#6)",
/// ];
/// assert_eq!(sample, result, "Wrapped enum");
/// ```
/// ## Unit-like struct wrapper
/// We can use bitfield type defined as unit-like struct in the same way as for
/// [enum](#enum-wrapper)
/// ```
/// # use std::{array, fmt, slice};
/// # use bitfield_layout::{BitFieldLayout, BitField, Layout};
/// 
/// // Unit-like struct without value
/// struct Status;
/// // Bind flags layout to this struct
/// impl Status {
///     const LAYOUT: [&'static str; 8] = [
///         "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7",
///     ];
/// }
/// // Implement layout trait
/// impl Layout for Status {
///     type Layout = core::slice::Iter<'static, &'static str>;
///     fn layout() -> Self::Layout { Status::LAYOUT.iter() }
/// }
/// 
/// let bf: BitField<Status, u8> = BitField::new(42);
/// // Get formatted strings from flags iteartor
/// let result = bf.flags()
///     .map(|f| format!("{:#}", f.value))
///     .collect::<Vec<_>>();
/// let sample = vec!["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7"];
/// assert_eq!(sample, result, "Simple unit-like struct");
/// 
/// ```
/// ## Unit-like struct with associated constants
/// Also we can use unit-like struct with associated constant flags. This will gave us feauture to has
/// marked bits. This realisation somewhere in beetween enum and simple unit-like struct.
/// ```
/// # use std::{array, fmt, slice};
/// # use bitfield_layout::{BitFieldLayout, BitField, Layout};
/// 
/// 
/// // Unit-like struct without value
/// struct Status;
/// // Implement layout. You can leave comments on every item. For example, you can use bit id as
/// // Status::ONE.
/// impl Status {
///     const ONE: &'static str = "One";
///     const TWO: &'static str = "Two";
///     const THREE: &'static str = "Three";
///     const FOUR: &'static str = "Four";
///     const RESERVED: &'static str = "Reserved";
///     const UNKNOWN: &'static str = "Unknown";
/// 
///     const LAYOUT: [&'static str; 8] = [
///         Self::ONE,
///         Self::TWO,
///         Self::THREE,
///         Self::FOUR,
///         Self::RESERVED,
///         Self::RESERVED,
///         Self::RESERVED,
///         Self::UNKNOWN,
///     ];
/// }
/// // Implement layout trait
/// impl Layout for Status {
///     type Layout = core::slice::Iter<'static, &'static str>;
///     fn layout() -> Self::Layout { Status::LAYOUT.iter() }
/// }
/// 
/// let bf: BitField<Status, u8> = BitField::new(0b00001000);
/// let result = bf.flags()
///     .find(|f| f.is_set)
///     .map(|f| f.value)
///     .unwrap();
/// assert_eq!(Status::FOUR, *result, "Enumeration");
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct BitField<M, T> {
    _marker: core::marker::PhantomData<M>,
    pub value: T,
}
impl<M, T> BitField<M, T> {
    pub fn new(value: T) -> Self {
        Self {
            _marker: core::marker::PhantomData,
            value
        }
    }
}
impl<M: Layout, T> Layout for BitField<M, T> {
    type Layout = M::Layout;
    fn layout() -> Self::Layout { M::layout() }
}
impl<M: Layout, T: Copy + IntoBits + FromBits> BitFieldLayout for BitField<M, T> {
    type Value = T;
    fn get(&self) -> Self::Value { self.value }
    fn set(&mut self, new: Self::Value) { self.value = new; }
}
impl<M, T> ops::BitAnd for BitField<M, T>
where
    M: Layout,
    T: Copy + IntoBits + FromBits + ops::BitAnd<Output = T>,
{
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        Self::new(self.get() & rhs.get())
    }
}
impl<M, T> ops::BitAndAssign for BitField<M, T>
where
    M: Layout,
    T: Copy + IntoBits + FromBits + ops::BitAnd<Output = T>,
{
    fn bitand_assign(&mut self, rhs: Self) {
        *self = Self::new(self.get() & rhs.get())
    }
}
impl<M, T> ops::BitOr for BitField<M, T>
where
    M: Layout,
    T: Copy + IntoBits + FromBits + ops::BitOr<Output = T>,
{
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        Self::new(self.get() | rhs.get())
    }
}
impl<M, T> ops::BitOrAssign for BitField<M, T>
where
    M: Layout,
    T: Copy + IntoBits + FromBits + ops::BitOr<Output = T>,
{
    fn bitor_assign(&mut self, rhs: Self) {
        *self = Self::new(self.get() | rhs.get())
    }
}
impl<M, T> ops::BitXor for BitField<M, T>
where
    M: Layout,
    T: Copy + IntoBits + FromBits + ops::BitXor<Output = T>,
{
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self::new(self.get() ^ rhs.get())
    }
}
impl<M, T> ops::BitXorAssign for BitField<M, T>
where
    M: Layout,
    T: Copy + IntoBits + FromBits + ops::BitXor<Output = T>,
{
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = Self::new(self.get() ^ rhs.get())
    }
}



#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
mod tests {
    use std::prelude::v1::*;
    use pretty_assertions::assert_eq;
    use super::*;

    #[test]
    fn bits() {
        let bits = Bits::new([13,42].iter().cloned());
        let sample = vec![
            true, false, true, true, false, false, false, false,
            false, true, false, true, false, true, false, false,
        ];
        let result = bits.collect::<Vec<_>>();
        assert_eq!(sample, result, "Bits");
    }

    #[test]
    fn into_bits() {
        assert_eq!(vec![false,true,false,true], 42u8.into_bits().take(4).collect::<Vec<_>>(), "u8");
        assert_eq!(vec![false,true,false,true], 42u16.into_bits().take(4).collect::<Vec<_>>(), "u16");
        assert_eq!(vec![false,true,false,true], 42u32.into_bits().take(4).collect::<Vec<_>>(), "u32");
        assert_eq!(vec![false,true,false,true], 42u64.into_bits().take(4).collect::<Vec<_>>(), "u64");
        assert_eq!(vec![false,true,false,true], 42u128.into_bits().take(4).collect::<Vec<_>>(), "u128");
        assert_eq!(vec![false,true,false,true], [42u8,1,2].into_bits().take(4).collect::<Vec<_>>(), "[u8;3]");
        assert_eq!(vec![false,true,false,true], [42u16,1,2].into_bits().take(4).collect::<Vec<_>>(), "[u16;3]");
        assert_eq!(vec![false,true,false,true], [42u32,1,2].into_bits().take(4).collect::<Vec<_>>(), "[u32;3]");
        assert_eq!(vec![false,true,false,true], [42u64,1,2].into_bits().take(4).collect::<Vec<_>>(), "[u64;3]");
        assert_eq!(vec![false,true,false,true], [42u128,1,2].into_bits().take(4).collect::<Vec<_>>(), "[u128;3]");
    }

    #[test]
    fn from_bits() {
        assert_eq!(42, u8::from_bits(42u8.into_bits()), "u8");
        assert_eq!(42, u16::from_bits(42u16.into_bits()), "u16");
        assert_eq!(42, u32::from_bits(42u32.into_bits()), "u32");
        assert_eq!(42, u64::from_bits(42u64.into_bits()), "u64");
        assert_eq!(42, u128::from_bits(42u128.into_bits()), "u128");
        assert_eq!([42;3], <[u8;3]>::from_bits([42u8;3].into_bits()), "[u8;3]");
        assert_eq!([42;3], <[u16;3]>::from_bits([42u16;3].into_bits()), "[u16;3]");
        assert_eq!([42;3], <[u32;3]>::from_bits([42u32;3].into_bits()), "[u32;3]");
        assert_eq!([42;3], <[u64;3]>::from_bits([42u64;3].into_bits()), "[u64;3]");
        assert_eq!([42;3], <[u128;3]>::from_bits([42u128;3].into_bits()), "[u128;3]");
    }

    #[test]
    fn flags() {
        let flags = Flags::new(
            ["Flag 1","Flag 2","Flag 3","Flag 4","Flag 5","Flag 6","Flag 7","Flag 8",]
                .iter(),
            [ false,   true,    false,   true,    true,    false,   false,   false, ]
                .iter().cloned(),
        );
        let sample = vec!["Flag 2","Flag 4","Flag 5",];
        let result = flags.filter_map(|f| Some(*f.value).filter(|_| f.is_set)).collect::<Vec<_>>();
        assert_eq!(sample, result, "Flags");
    }

    #[test]
    fn diff() {
        let layout = ["Flag 1","Flag 2","Flag 3","Flag 4","Flag 5","Flag 6","Flag 7","Flag 8",];
        let flags0 = Flags::new(
            layout.iter(),
            [ false,   true,    false,   true,    true,    false,   false,   false, ]
                .iter().cloned(),
        );
        let flags1 = Flags::new(
            layout.iter(),
            [ false,   true,    false,   false,    true,    false,   true,   false, ]
                .iter().cloned(),
        );
        let sample = vec![
            Either::Left((3, &"Flag 4")),
            Either::Right((6, &"Flag 7"))
        ];
        let result = Diff::new(flags0, flags1).collect::<Vec<_>>();
        assert_eq!(sample, result, "Diff");
    }

    #[test]
    fn bitfield_bitwise() {
        #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
        struct Simple;
        // Dumb layout
        impl Layout for Simple {
            type Layout = core::iter::Empty<()>;
            fn layout() -> Self::Layout { std::iter::empty() }
        }

        let bitand_result: BitField<Simple, u8> = BitField::new(42) & BitField::new(0b1111);
        assert_eq!(BitField::<Simple, u8>::new(0b1010), bitand_result, "BitAnd");

        let mut bitand_assign_result: BitField<Simple, u8> = BitField::new(42);
        bitand_assign_result &= BitField::new(0b1111);
        assert_eq!(BitField::<Simple, u8>::new(0b1010), bitand_assign_result, "BitAndAssign");

        let bitor_result: BitField<Simple, u8> = BitField::new(42) | BitField::new(0b1111);
        assert_eq!(BitField::<Simple, u8>::new(0b101111), bitor_result, "BitOr");

        let mut bitor_assign_result: BitField<Simple, u8> = BitField::new(42);
        bitor_assign_result |= BitField::new(0b1111);
        assert_eq!(BitField::<Simple, u8>::new(0b101111), bitor_assign_result, "BitOrAssign");

        let bitxor_result: BitField<Simple, u8> = BitField::new(42) ^ BitField::new(0b1111);
        assert_eq!(BitField::<Simple, u8>::new(0b100101), bitxor_result, "BitXor");

        let mut bitxor_assign_result: BitField<Simple, u8> = BitField::new(42);
        bitxor_assign_result ^= BitField::new(0b1111);
        assert_eq!(BitField::<Simple, u8>::new(0b100101), bitxor_assign_result, "BitXorAssign");
    }
}
