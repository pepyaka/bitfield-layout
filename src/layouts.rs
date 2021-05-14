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
/// use std::{array, fmt, slice};
/// use bitfield_layout::{Layout, Bytes, BitFieldLayout, DualView};
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
/// 
/// impl Layout for StatusRegister {
///     type Layout = slice::Iter<'static, DualView<'static>>;
///     fn layout() -> Self::Layout { StatusRegister::LAYOUT.iter() }
/// }
/// impl Bytes for StatusRegister {
///     type Bytes = array::IntoIter<u8, 1>;
///     fn bytes(&self) -> Self::Bytes { array::IntoIter::new(self.0.to_ne_bytes()) }
/// }
/// impl BitFieldLayout for StatusRegister {}
/// 
/// for f in StatusRegister(0b10000001).flags() {
///     println!("Name: {}\nDescription: {:#}\n", f.value, f.value)
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
/// This struct may used for each record in bitfield layout
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
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





//#[macro_export]
//macro_rules! layout  {
//    // DualView
//    (item = DualView; [] -> [$($output:tt)*]) => {
//        [$($output)*].iter()
//    };
//    (item = DualView; [$m:literal $d:literal, $($input:tt)*] -> [$($output:tt)*]) => {
//        layout!(item = DualView; [$($input)*] -> [$($output)* layouts::DualView($m, $d),])
//    };
//    (item = DualView; [$m:literal, $($input:tt)*] -> [$($output:tt)*]) => {{
//        layout!(item = DualView; [$($input)*] -> [$($output)* layouts::DualView($m, $m),])
//    }};
//    ([DualView]; $($input:tt)*) => {
//        layout!(item = DualView; [$($input)*] -> [])
//    };
//
//    // FlagType
//    (item = FlagType; array = $a:expr; index = $i:expr;) => {{ $a }};
//    (item = FlagType; array = $a:expr; index = $i:expr; $m:literal: $n:expr, $($input:tt)*) => {{
//        let mut result = layout!(item = FlagType; array = $a; index = $i + $n; $($input)*);
//        let mut i = $i;
//        while i < $i + $n {
//            result[i] = FlagType::Reserved($m);
//            i += 1;
//        }
//        result
//    }};
//    (item = FlagType; array = $a:expr; index = $i:expr; $m:literal $d:literal, $($input:tt)*) => {{
//        let mut result = layout!(item = FlagType; array = $a; index = $i + 1; $($input)*);
//        result[$i] = FlagType::Significant($m, $d);
//        result
//    }};
//    (item = FlagType; array = $a:expr; index = $i:expr; $m:literal, $($input:tt)*) => {{
//        let mut result = layout!(item = FlagType; array = $a; index = $i + 1; $($input)*);
//        result[$i] = FlagType::Significant($m, $m);
//        result
//    }};
//    ([FlagType; $n:expr]; $($input:tt)*) => {{
//        const LAYOUT: [FlagType; $n] =
//            layout!(item = FlagType; array = [FlagType::Unknown; $n]; index = 0; $($input)*);
//        LAYOUT.iter()
//    }};
//
//    // Utils
//    (@as_expr $e:expr) => { $e };
//}



#[cfg(test)]
mod tests {
    //#![feature(trace_macros)]
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
        struct EightFlags(u8);
        impl EightFlags {
            const LAYOUT: [DualView<'static>; 8] = [
                DualView(
                    "Carry flag",
                    "Enables numbers larger than a single word to be added/subtracted by
                    carrying a binary digit from a less significant word to the least
                    significant bit of a more significant word as needed."
                ),
                DualView(
                    "Zero flag",
                    "Indicates that the result of an arithmetic or logical operation
                    (or, sometimes, a load) was zero."
                ),
                DualView(
                    "Interrupt flag",
                    "Indicates whether interrupts are enabled or masked."
                ),
                DualView(
                    "Decimal flag",
                    "Indicates that a bit carry was produced between the nibbles as a
                    result of the last arithmetic operation."
                ),
                DualView(
                    "Break flag",
                    "It can be examined as a value stored on the stack."
                ),
                DualView("Unused", "Unused"),
                DualView(
                    "Overflow flag",
                    "Indicates that the signed result of an operation is too large to
                    fit in the register width using two's complement representation."
                ),
                DualView(
                    "Negative flag",
                    "Indicates that the result of a mathematical operation is negative."
                ),
            ];
        }
        
        impl Layout for EightFlags {
            type Layout = slice::Iter<'static, DualView<'static>>;
            fn layout() -> Self::Layout { EightFlags::LAYOUT.iter() }
        }
        impl Bytes for EightFlags {
            type Bytes = array::IntoIter<u8, 1>;
            fn bytes(&self) -> Self::Bytes { array::IntoIter::new(self.0.to_ne_bytes()) }
        }
        impl BitFieldLayout for EightFlags {}
        
        for f in EightFlags(42).flags() {
            println!("Name: {}\nDescription: {:#}\n", f.value, f.value)
        }
    }
}
