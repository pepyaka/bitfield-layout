//! This crate is yet another bitfield handling implementation.
//! 
//! The main goal of this crate - provide binding for various data to every bit (flag) within bitfield layout.
//! In many cases bitfield data are read-only and every bit (flag) has some meaning.
//! Then you getting bitfield data it's useful to get meaning and/or description of setted flags.
//! 
//! This crate provides basic trait [BitFieldLayout] that provides convenient methods for getting flags
//! and it meaning of user defined structures or enums. Also there is module [layouts] with accessory
//! structs and macros.
//! 
//! # Example: simple string
//! Bits layout within bitfield may be associated with it meaning in many ways. The simple case - each
//! bit (flag) has simple string description.
//! 
//! ```
//! use std::{array, fmt, slice};
//! use bitfield_layout::{Layout, Bytes, ToBytes, BitFieldLayout};
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
//! // Represent type's value as bytes
//! impl Bytes for Simple {
//!     type Bytes = array::IntoIter<u8, 1>;
//!     fn bytes(&self) -> Self::Bytes {
//!         self.0.to_bytes()
//!     }
//! }
//! // Main trait implementation
//! impl BitFieldLayout for Simple {}
//! 
//! // Now we can use methods provided by trait
//! 
//! // Show full data layout (just show flag meanings that we defined)
//! for l in Simple::layout() {
//!     println!("{}", l);
//! }
//! 
//! // Show every bit (flag) state
//! let simple = Simple(0b10101010);
//! for (n, b) in simple.bits().enumerate() {
//!     println!("Bit #{}: {}", n, if b { "Is set" } else { "Not set" });
//! }
//! 
//! // Show bit (flag) state and it meaning
//! for f in simple.flags() {
//!     println!("Flag {} is {}", f.value, f.is_set);
//! }
//! 
//! // Show difference between two bitfield values
//! let other = Simple(0b11001100);
//! for diff in simple.diff(other) {
//!     println!("Diff: {:?}", diff);
//! }
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
//! use bitfield_layout::{Layout, Bytes, ToBytes, BitFieldLayout};
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
//!             "Enables numbers larger than a single word to be added/subtracted by
//!             carrying a binary digit from a less significant word to the least
//!             significant bit of a more significant word as needed."
//!         ),
//!         NameAndDescription(
//!             "Zero flag",
//!             "Indicates that the result of an arithmetic or logical operation
//!             (or, sometimes, a load) was zero."
//!         ),
//!         NameAndDescription(
//!             "Interrupt flag",
//!             "Indicates whether interrupts are enabled or masked."
//!         ),
//!         NameAndDescription(
//!             "Decimal flag",
//!             "Indicates that a bit carry was produced between the nibbles as a
//!             result of the last arithmetic operation."
//!         ),
//!         NameAndDescription(
//!             "Break flag",
//!             "It can be examined as a value stored on the stack."
//!         ),
//!         NameAndDescription("Unused", "Unused"),
//!         NameAndDescription(
//!             "Overflow flag",
//!             "Indicates that the signed result of an operation is too large to
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
//! // Implement iterator through bytes
//! impl Bytes for StatusRegister {
//!     // Last '1' indicate number of iterator items.
//!     type Bytes = array::IntoIter<u8, 1>;
//!     // Convert one byte value (u8) to one item iterator
//!     fn bytes(&self) -> Self::Bytes {
//!         self.0.to_bytes()
//!     }
//! }
//! // Bitfield trait implementation
//! impl BitFieldLayout for StatusRegister {}
//! 
//! // For example our value has setted Carry and Negative flags
//! let status = StatusRegister(0b10000001);
//! 
//! // Print only setted flag name and description
//! for f in status.flags() {
//!     if f.is_set {
//!         println!("Name: {}\nDescription: {:#}\n", f.value, f.value)
//!     }
//! }
//! ```
//! 
//! ---
//! There are more examples in [layouts] and [BitField]




#![no_std]

use core::array;

use either::Either;

#[macro_use]
pub mod layouts;
pub use layouts::*;


/// Main trait for creating bitfield 
///
/// In general you need implement this trait and its dependencies [Layout] + [Bytes]. 
/// This trait already implemented for [BitField].
pub trait BitFieldLayout: Layout + Bytes {
    /// Return iterator through bitfield value bits. Every bit represents as bool value
    fn bits(&self) -> Bits<Self::Bytes> {
        Bits::new(self.bytes())
    }
    /// Return iterator through bitfield value flags. Every flag contains bit state (set or unset)
    /// and item (record) value - string in simple case
    fn flags(&self) -> Flags<Self::Layout, Bits<Self::Bytes>> {
        Flags::new(Self::layout(), self.bits())
    }
    /// Helps to find difference between two bitfield values
    fn diff(&self, other: Self) -> Diff<Self::Layout, Bits<Self::Bytes>>
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

/// Value iterable as bytes
pub trait Bytes {
    /// Bytes iterator. Every bitfield data should be convertable to bytes
    type Bytes: Iterator<Item = u8>;
    /// Return iterator through bitfield type value bytes 
    fn bytes(&self) -> Self::Bytes;
}

/// Simple trait to converting unsigned integers to byte array
pub trait ToBytes {
    type Bytes: Iterator<Item = u8>;
    /// Contain one method to convert any reasonable bitfield value representation to bytes
    /// iterator
    fn to_bytes(&self) -> Self::Bytes;
}
impl ToBytes for u8 {
    type Bytes = array::IntoIter<u8, 1>;
    fn to_bytes(&self) -> Self::Bytes {
        array::IntoIter::new(self.to_ne_bytes())
    }
}
impl ToBytes for u16 {
    type Bytes = array::IntoIter<u8, 2>;
    fn to_bytes(&self) -> Self::Bytes {
        array::IntoIter::new(self.to_ne_bytes())
    }
}
impl ToBytes for u32 {
    type Bytes = array::IntoIter<u8, 4>;
    fn to_bytes(&self) -> Self::Bytes {
        array::IntoIter::new(self.to_ne_bytes())
    }
}
impl ToBytes for u64 {
    type Bytes = array::IntoIter<u8, 8>;
    fn to_bytes(&self) -> Self::Bytes {
        array::IntoIter::new(self.to_ne_bytes())
    }
}
impl ToBytes for u128 {
    type Bytes = array::IntoIter<u8, 16>;
    fn to_bytes(&self) -> Self::Bytes {
        array::IntoIter::new(self.to_ne_bytes())
    }
}
impl<const N: usize> ToBytes for [u8; N] {
    type Bytes = array::IntoIter<u8, N>;
    fn to_bytes(&self) -> Self::Bytes {
        array::IntoIter::new(self.clone())
    }
}


/// An iterator through value bits
#[derive(Debug, Clone)]
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
impl<T> From<(T, bool)> for Flag<T> {
    fn from((value, is_set): (T, bool)) -> Self {
        Self { value, is_set }
    }
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
/// value field: enums and unit-like structs.
///
/// ## Enum wrapper usage
/// Using enumeration as bitfield type has the following advantage - you can bind bit (flag) to one of
/// enum variants.
/// ```
/// # use std::{array, fmt, slice};
/// # use bitfield_layout::{BitFieldLayout, BitField, Layout};
/// 
/// // Creating new bitfield type
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
/// We can use bitfield type defined as unit-like struct in the same way
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
pub struct BitField<M, T: ToBytes> {
    _marker: core::marker::PhantomData<M>,
    pub value: T,
}
impl<M, T: ToBytes> BitField<M, T> {
    pub fn new(value: T) -> Self {
        Self {
            _marker: core::marker::PhantomData,
            value
        }
    }
}
impl<M: Layout, T: ToBytes> Layout for BitField<M, T> {
    type Layout = M::Layout;
    fn layout() -> Self::Layout { M::layout() }
}
impl<M: Layout, T: ToBytes> Bytes for BitField<M, T> {
    type Bytes = <T as ToBytes>::Bytes;
    fn bytes(&self) -> Self::Bytes { self.value.to_bytes() }
}
impl<M: Layout, T: ToBytes> BitFieldLayout for BitField<M, T> {}


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
    fn to_bytes() {
        assert_eq!(13u8.to_bytes().collect::<Vec<_>>(), vec![13], "ToBytes: u8");
        assert_eq!(13u16.to_bytes().collect::<Vec<_>>(), vec![13,0], "ToBytes: u16");
        assert_eq!(13u32.to_bytes().collect::<Vec<_>>(), vec![13,0,0,0], "ToBytes: u32");
        assert_eq!(13u64.to_bytes().collect::<Vec<_>>(), vec![13,0,0,0,0,0,0,0], "ToBytes: u64");
        assert_eq!(13u128.to_bytes().collect::<Vec<_>>(), vec![13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], "ToBytes: u128");
        assert_eq!([13u8].to_bytes().collect::<Vec<_>>(), vec![13], "ToBytes: [u8; 1]");
        assert_eq!([13u8,42u8,73u8].to_bytes().collect::<Vec<_>>(), vec![13, 42, 73], "ToBytes: [u8; 3]");
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
}
