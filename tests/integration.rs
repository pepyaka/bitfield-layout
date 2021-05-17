use std::{array};

use either::Either;
use pretty_assertions::assert_eq;

use bitfield_layout::*;


#[test]
fn simple() {
    struct Simple(u8);
    impl<'a> Simple {
        const LAYOUT: &'a [&'a str] = &[
            "A", "B", "C", "D", "E", "F", "G", "H"
        ];
    }
    impl Layout for Simple {
        type Layout = std::slice::Iter<'static, &'static str>;
        fn layout() -> Self::Layout { Self::LAYOUT.iter() }
    }
    impl Bytes for Simple {
        type Bytes = array::IntoIter<u8, 1>;
        fn bytes(&self) -> Self::Bytes { self.0.to_bytes() }
    }
    impl BitFieldLayout for Simple {}

    let layout_sample = vec!["A", "B", "C", "D", "E", "F", "G", "H"];
    let layout_result = Simple::layout().map(|bf| format!("{:#}", bf)).collect::<Vec<_>>();
    assert_eq!(layout_sample, layout_result, "Layout");

    let simple = Simple(0b00011000);

    let bits_sample = vec![false,false,false,true,true,false,false,false];
    let bits_result = simple.bits().collect::<Vec<_>>();
    assert_eq!(bits_sample, bits_result, "Bits");

    let flags_sample = vec![
        Flag { is_set: true, value: &"D" },
        Flag { is_set: true, value: &"E" },
    ];
    let flags_result = simple.flags().filter(|f| f.is_set).collect::<Vec<_>>();
    assert_eq!(flags_sample, flags_result, "Flags");

    let diff_sample = vec![
        Either::Right((2, &"C")),
        Either::Left((4, &"E")),
    ];
    let diff_result = simple.diff(Simple(0b00001100)).collect::<Vec<_>>();
    assert_eq!(diff_sample, diff_result, "Diff");
}
