import Std

/-! Handwritten GF64 bitvector specification. This is not a Rust refinement. -/

namespace BulksketchProofs.Field

/-- Multiply a 64-bit coefficient word by the low modulus `1 + X + X^3 + X^4`,
retaining its low 64 coefficients. -/
def fold64 (high : BitVec 64) : BitVec 64 :=
  high ^^^ (high <<< 1) ^^^ (high <<< 3) ^^^ (high <<< 4)

/-- High coefficients of the first low-modulus product. -/
def overflow64 (high : BitVec 64) : BitVec 64 :=
  (high >>> 63) ^^^ (high >>> 61) ^^^ (high >>> 60)

/-- Two-fold reduction, grouped mathematically rather than by Rust expression syntax. -/
def reduceFold64 (low high : BitVec 64) : BitVec 64 :=
  low ^^^ fold64 high ^^^ fold64 (overflow64 high)

/-- Untruncated low-modulus product in 128 coefficient bits. -/
def fold128 (high : BitVec 64) : BitVec 128 :=
  high.setWidth 128 ^^^ (high.setWidth 128 <<< 1) ^^^
    (high.setWidth 128 <<< 3) ^^^ (high.setWidth 128 <<< 4)

/-- The polynomial represented by a low/high word pair. -/
def join128 (low high : BitVec 64) : BitVec 128 :=
  low.setWidth 128 ^^^ (high.setWidth 128 <<< 64)

/-- Exact carry-less product with `X^64 + X^4 + X^3 + X + 1`.
The coefficient degree is at most 127, so 128 bits suffice. -/
def modulusMultiple128 (quotient : BitVec 64) : BitVec 128 :=
  (quotient.setWidth 128 <<< 64) ^^^ fold128 quotient


end BulksketchProofs.Field
