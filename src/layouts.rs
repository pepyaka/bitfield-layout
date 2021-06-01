//! This module contains useful structures that can be used as meaning of bitflag
//!
//!

use core::fmt;

/// Simple structure for basic and alternate string view
/// 
/// This struct may be used in most cases of crate using. 
/// We can rewrite [6502 status register example](super#example-status-register-of-mos-technology-6502)
/// using this struct
/// ```
/// # use std::{array, fmt, slice, ops::Deref};
/// # use bitfield_layout::{Layout, BitFieldLayout, DualView};
/// 
/// struct StatusRegister(u8);
/// impl StatusRegister {
///     const LAYOUT: [DualView<'static>; 8] = [
///         DualView(
///             "Carry flag",
///             "Enables numbers larger than a single word to be added/subtracted by
///             carrying a binary digit from a less significant word to the least
///             significant bit of a more significant word as needed."
///         ),
///         DualView(
///             "Zero flag",
///             "Indicates that the result of an arithmetic or logical operation
///             (or, sometimes, a load) was zero."
///         ),
///         DualView(
///             "Interrupt flag",
///             "Indicates whether interrupts are enabled or masked."
///         ),
///         DualView(
///             "Decimal flag",
///             "Indicates that a bit carry was produced between the nibbles as a
///             result of the last arithmetic operation."
///         ),
///         DualView(
///             "Break flag",
///             "It can be examined as a value stored on the stack."
///         ),
///         DualView("Unused", "Unused"),
///         DualView(
///             "Overflow flag",
///             "Indicates that the signed result of an operation is too large to
///             fit in the register width using two's complement representation."
///         ),
///         DualView(
///             "Negative flag",
///             "Indicates that the result of a mathematical operation is negative."
///         ),
///     ];
/// }
/// impl Layout for StatusRegister {
///     type Layout = slice::Iter<'static, DualView<'static>>;
///     fn layout() -> Self::Layout { StatusRegister::LAYOUT.iter() }
/// }
/// impl BitFieldLayout for StatusRegister {
///     type Value = u8;
///     fn get(&self) -> Self::Value { self.0 }
///     fn set(&mut self, new: Self::Value) { self.0 = new; }
/// }
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct DualView<'a>(pub &'a str, pub &'a str);
impl<'a> fmt::Display for DualView<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = if f.alternate() { self.1 } else { self.0 };
        write!(f, "{}", s)
    }
}

/// Complex enumeration for several types of bit (flag)
///
/// This enum variants may be used to show difference beetween meaningful and reserved flags.
/// ```
/// # use core::{slice,array};
/// # use pretty_assertions::assert_eq;
/// # use bitfield_layout::{Layout, BitFieldLayout, FlagType, layout};
///
/// // Bitfield type definition
/// struct Light(u8);
/// impl Light {
///     const LAYOUT: [FlagType<'static>; 8] = [
///         FlagType::Significant("Red", "Red is the color at the long wavelength end"),
///         FlagType::Significant("Blue", "Blue is one of the three primary colours of pigments"),
///         FlagType::Significant("Green", "Green is the color between blue and yellow"),
///         FlagType::Reserved("Invisible"),
///         FlagType::ShouldBe0,
///         FlagType::ShouldBe1,
///         FlagType::Unknown,
///         FlagType::Undefined,
///     ];
/// }
/// // Implementation
/// impl Layout for Light {
///     type Layout = slice::Iter<'static, FlagType<'static>>;
///     fn layout() -> Self::Layout { Light::LAYOUT.iter() }
/// }
/// impl BitFieldLayout for Light {
///     type Value = u8;
///     fn get(&self) -> Self::Value { self.0 }
///     fn set(&mut self, new: Self::Value) { self.0 = new; }
/// }
///
/// // Value assignment
/// let white = Light(0b00100111);
///
/// let result = white.flags()
///     .enumerate()
///     .find(|(n, f)| n == &5 && f.is_set == true)
///     .map(|(_, f)| *f.value);
/// let sample = Some(FlagType::ShouldBe1);
///
/// assert_eq!(sample, result);
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum FlagType<'a> {
    /// Has two strings - one for meaning, other for long description
    Significant(&'a str, &'a str),
    /// Reserved bit (flag) may has different types of reservation. Ex: OEM and Future using 
    Reserved(&'a str),
    /// Should always be set
    ShouldBe0,
    /// Should always be unset
    ShouldBe1,
    /// Unknown for current specification
    Unknown,
    /// Undefined in current specification
    Undefined,
}
impl<'a> fmt::Display for FlagType<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self, f.alternate()) {
            (Self::Significant(s, _), false) => write!(f, "{}", s),
            (Self::Significant(_, s), true) => write!(f, "{}", s),
            (Self::Reserved(s), _) => write!(f, "{}", s),
            (Self::ShouldBe0, _) => write!(f, "Should be 0"),
            (Self::ShouldBe1, _) => write!(f, "Should be 1"),
            (Self::Unknown, _) => write!(f, "Unknown"),
            (Self::Undefined, _) => write!(f, "Undefined"),
        }
    }
}




/// Fast defining of useful types
///
/// This macro helps to implement [crate::BitFieldLayout] trait and create associated const layout.
/// Macro may be used for following data types:
/// - [DualView](#dualview)
/// - [FlagType](#flagtype)
///
/// ## DualView
/// 
/// ```
/// # use core::{slice,array};
/// # use bitfield_layout::{Layout, BitFieldLayout, DualView, layout};
/// # fn main() {
///
/// // Data created by macro
/// let macro_data = {
///     layout!(
///         DualView;
///         struct Letters(u8);
///         "a",
///         "b" "B",
///         "c",
///         "d",
///         "e",
///         "f" "F",
///         "g" "G",
///         "h" "H",
///     );
///
///     Letters(42).flags()
/// };
/// // Expands to:
/// let manual_data = {
///     struct Letters(u8);
///     impl Letters {
///         const LAYOUT: [DualView<'static>; 8] = [
///             DualView("a", "a"),
///             DualView("b", "B"),
///             DualView("c", "c"),
///             DualView("d", "d"),
///             DualView("e", "e"),
///             DualView("f", "F"),
///             DualView("g", "G"),
///             DualView("h", "H"),
///         ];
///     }
///     
///     impl Layout for Letters {
///         type Layout = slice::Iter<'static, DualView<'static>>;
///         fn layout() -> Self::Layout { Letters::LAYOUT.iter() }
///     }
///     impl BitFieldLayout for Letters {
///         type Value = u8;
///         fn get(&self) -> Self::Value { self.0 }
///         fn set(&mut self, new: Self::Value) { self.0 = new; }
///     }
///
///     Letters(42).flags()
/// };
///
/// assert_eq!(macro_data.collect::<Vec<_>>(), manual_data.collect::<Vec<_>>());
/// # }
/// ```
///
/// ## FlagType
/// ```
/// # use core::{slice,array};
/// # use pretty_assertions::assert_eq;
/// # use bitfield_layout::{Layout, BitFieldLayout, FlagType, layout};
/// # fn main() {
/// let macro_data = {
///     layout!(
///         FlagType;
///         struct EightFlags(u8);
///         "Significant: meaning",
///         "Significant: meaning" "Significant: description",
///         "Reserved: 2 bits": 2,
///         "Reserved: shouldn't exists": 0,
///         ShouldBe0,
///         ShouldBe1,
///         Unknown,
///         Undefined,
///     );
///
///     EightFlags(73).flags()
/// };
/// // Expands to:
/// let manual_data = {
///     struct EightFlags(u8);
///     impl EightFlags {
///         const LAYOUT: [FlagType<'static>; 8] = [
///             FlagType::Significant("Significant: meaning", "Significant: meaning"),
///             FlagType::Significant("Significant: meaning", "Significant: description"),
///             FlagType::Reserved("Reserved: 2 bits"),
///             FlagType::Reserved("Reserved: 2 bits"),
///             FlagType::ShouldBe0,
///             FlagType::ShouldBe1,
///             FlagType::Unknown,
///             FlagType::Undefined,
///         ];
///     }
///     
///     impl Layout for EightFlags {
///         type Layout = slice::Iter<'static, FlagType<'static>>;
///         fn layout() -> Self::Layout { EightFlags::LAYOUT.iter() }
///     }
///     impl BitFieldLayout for EightFlags {
///         type Value = u8;
///         fn get(&self) -> Self::Value { self.0 }
///         fn set(&mut self, new: Self::Value) { self.0 = new; }
///     }
///
///     EightFlags(73).flags()
/// };
///
/// assert_eq!(macro_data.collect::<Vec<_>>(), manual_data.collect::<Vec<_>>());
/// # }
/// ```
#[macro_export]
macro_rules! layout  {
    // DualView
    (item = DualView; [] -> [$($output:tt)*]) => {
        [$($output)*]
    };
    (item = DualView; [$m:literal $d:literal, $($input:tt)*] -> [$($output:tt)*]) => {
        layout!(item = DualView; [$($input)*] -> [$($output)* DualView($m, $d),])
    };
    (item = DualView; [$m:literal, $($input:tt)*] -> [$($output:tt)*]) => {{
        layout!(item = DualView; [$($input)*] -> [$($output)* DualView($m, $m),])
    }};
    (DualView; $vis:vis $ident:ident $name:ident($value:tt); $($input:tt)*) => {
        $vis $ident $name($value);
        impl $name {
            const LAYOUT: &'static [DualView<'static>] =
                &layout!(item = DualView; [$($input)*] -> []);
        }
        impl Layout for $name {
            type Layout = slice::Iter<'static, DualView<'static>>;
            fn layout() -> Self::Layout { $name::LAYOUT.iter() }
        }
        impl BitFieldLayout for $name {
            type Value = $value;
            fn get(&self) -> Self::Value { self.0 }
            fn set(&mut self, new: Self::Value) { self.0 = new; }
        }
    };

    // FlagType
    (item = FlagType; array = $a:expr; index = $i:expr;) => {{ $a }};
    (item = FlagType; array = $a:expr; index = $i:expr; Undefined, $($input:tt)*) => {{
        let mut result = layout!(item = FlagType; array = $a; index = $i + 1; $($input)*);
        result[$i] = FlagType::Undefined;
        result
    }};
    (item = FlagType; array = $a:expr; index = $i:expr; Unknown, $($input:tt)*) => {{
        let mut result = layout!(item = FlagType; array = $a; index = $i + 1; $($input)*);
        result[$i] = FlagType::Unknown;
        result
    }};
    (item = FlagType; array = $a:expr; index = $i:expr; ShouldBe1, $($input:tt)*) => {{
        let mut result = layout!(item = FlagType; array = $a; index = $i + 1; $($input)*);
        result[$i] = FlagType::ShouldBe1;
        result
    }};
    (item = FlagType; array = $a:expr; index = $i:expr; ShouldBe0, $($input:tt)*) => {{
        let mut result = layout!(item = FlagType; array = $a; index = $i + 1; $($input)*);
        result[$i] = FlagType::ShouldBe0;
        result
    }};
    (item = FlagType; array = $a:expr; index = $i:expr; $m:literal: $n:expr, $($input:tt)*) => {{
        let mut result = layout!(item = FlagType; array = $a; index = $i + $n; $($input)*);
        let mut i = $i;
        while i < $i + $n {
            result[i] = FlagType::Reserved($m);
            i += 1;
        }
        result
    }};
    (item = FlagType; array = $a:expr; index = $i:expr; $m:literal $d:literal, $($input:tt)*) => {{
        let mut result = layout!(item = FlagType; array = $a; index = $i + 1; $($input)*);
        result[$i] = FlagType::Significant($m, $d);
        result
    }};
    (item = FlagType; array = $a:expr; index = $i:expr; $m:literal, $($input:tt)*) => {{
        let mut result = layout!(item = FlagType; array = $a; index = $i + 1; $($input)*);
        result[$i] = FlagType::Significant($m, $m);
        result
    }};
    (FlagType; $vis:vis $ident:ident $name:ident($value:tt); $($input:tt)*) => {
        $vis $ident $name($value);
        impl $name {
            const LAYOUT: [FlagType<'static>; { layout!(@count_bytes $value) * 8 }] =
                layout!(
                    item = FlagType;
                    array = [FlagType::Unknown; { layout!(@count_bytes $value) * 8 }];
                    index = 0;
                    $($input)*
                );
        }
        impl Layout for $name {
            type Layout = core::slice::Iter<'static, FlagType<'static>>;
            fn layout() -> Self::Layout { $name::LAYOUT.iter() }
        }
        impl BitFieldLayout for $name {
            type Value = $value;
            fn get(&self) -> Self::Value { self.0 }
            fn set(&mut self, new: Self::Value) { self.0 = new; }
        }
    };

    // Utils
    (@as_expr $expr:expr) => { $expr };
    (@as_ty $ty:ty) => { $ty };
    (@count_bytes u8) => { 1 };
    (@count_bytes u16) => { 2 };
    (@count_bytes u32) => { 4 };
    (@count_bytes u64) => { 8 };
    (@count_bytes u128) => { 16 };
    (@count_bytes [u8; $n:expr]) => { $n };
}



#[cfg(test)]
mod tests {
    use std::prelude::v1::*;
    use std::{slice,};

    use pretty_assertions::assert_eq;
    use crate::*;


    #[test]
    fn dual_view() {
        let result = DualView("a", "A");
        assert_eq!("a", format!("{}", result));
        assert_eq!("A", format!("{:#}", result));
    }

    #[test]
    fn flag_type() {
        let significant = FlagType::Significant("s", "S");
        let reserved = FlagType::Reserved("r");
        assert_eq!("s", format!("{}", significant));
        assert_eq!("S", format!("{:#}", significant));
        assert_eq!("r", format!("{:#}", reserved));
    }

    #[test]
    fn layout_macro_dual_view() {
        layout!(
            DualView;
            struct Letters(u8);
            "a",
            "b" "B",
            "c",
            "d",
            "e",
            "f" "F",
            "g" "G",
            "h" "H",
        );
        let l0 = Letters(0b00000000);
        let l1 = Letters(0b00100000);
        let result = l0.diff(l1).next().unwrap();
        let sample = either::Either::Right((5, &DualView("f", "F")));
        assert_eq!(sample, result);
        layout!(
            DualView;
            pub struct Triple([u8; 3]);
            "a",
            "b" "B",
            "c",
            "d",
            "e",
            "f" "F",
            "g" "G",
            "h" "H",
        );
    }

    #[test]
    fn layout_macro_flag_type() {
        layout!(
            FlagType;
            struct EightFlags(u8);
            "Significant: meaning",
            "Significant: meaning" "Significant: description",
            "Reserved: 2 bits": 2,
            "Reserved: shouldn't exists": 0,
            ShouldBe0,
            ShouldBe1,
            Unknown,
            Undefined,
        );
        let ef0 = EightFlags(0b00000000);
        let ef1 = EightFlags(0b00100000);
        let result = ef0.diff(ef1).next().unwrap();
        let sample = either::Either::Right((5, &FlagType::ShouldBe1));
        assert_eq!(sample, result);
    }
}
