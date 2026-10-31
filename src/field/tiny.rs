//! Crate-private test fields for exhaustive decoder enumeration.
#![forbid(unsafe_code)]

use crate::{
    field::{BinaryField, sealed},
    types::FieldId,
};

// There is no tiny-field wire registration. The required trait slot uses the sole
// registered ID; SketchShape::new rejects every one of these by BITS before allocation.
macro_rules! test_field {
    ($name:ident, $bits:literal, $tail:literal, $modulus:literal) => {
        #[doc = $modulus]
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub(crate) struct $name;
        impl sealed::Sealed for $name {}
        impl BinaryField for $name {
            const BITS: u32 = $bits;
            const MODULUS_LOW: u64 = $tail;
            const WIRE_ID: FieldId = FieldId::Gf64;
            const MASK: u64 = (1 << $bits) - 1;
        }
    };
}

test_field!(Gf4, 2, 0x3, "GF(4), irreducible modulus Z^2 + Z + 1.");
test_field!(Gf16, 4, 0x3, "GF(16), irreducible modulus Z^4 + Z + 1.");
test_field!(
    Gf256,
    8,
    0x1b,
    "GF(256), irreducible modulus Z^8 + Z^4 + Z^3 + Z + 1."
);
test_field!(
    Gf65536,
    16,
    0x100b,
    "GF(65536), irreducible modulus Z^16 + Z^12 + Z^3 + Z + 1."
);
