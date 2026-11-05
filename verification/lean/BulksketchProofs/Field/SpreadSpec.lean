import BulksketchProofs.Field.ReductionSpec

/-!
# Bit-interleaving model and raw square layout

These handwritten definitions mirror the native `spread` shifts/masks and the
low/high-word assembly used by `square` at source revision
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`. They are mathematical bitvector
models. Connection to extracted Rust/Aeneas semantics is a separate obligation.
-/

namespace BulksketchProofs.Field

/-- Spread the low 32 input coefficients into the even positions of one word. -/
def spread64 (word : BitVec 64) : BitVec 64 :=
  let word := word &&& 0xffff_ffff
  let word := (word ||| (word <<< 16)) &&& 0x0000_ffff_0000_ffff
  let word := (word ||| (word <<< 8)) &&& 0x00ff_00ff_00ff_00ff
  let word := (word ||| (word <<< 4)) &&& 0x0f0f_0f0f_0f0f_0f0f
  let word := (word ||| (word <<< 2)) &&& 0x3333_3333_3333_3333
  (word ||| (word <<< 1)) &&& 0x5555_5555_5555_5555

/-- The 128 coefficient bits formed before reducing a field square. -/
def rawSquare128 (word : BitVec 64) : BitVec 128 :=
  join128 (spread64 word) (spread64 (word >>> 32))

end BulksketchProofs.Field
