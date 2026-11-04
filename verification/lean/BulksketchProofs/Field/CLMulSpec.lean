import BulksketchProofs.Field.ReductionSpec

/-!
Independent polynomial-coefficient specification of full 64-by-64 carryless
multiplication. All 128 output bits are retained before field reduction.
The definitions contain no source loop, table, trailing-zero operation, array
indexing, machine cast or generated application body.
-/

namespace BulksketchProofs.Field

/-- Product contributed by the first `count` coefficients of the right operand. -/
def clmulPrefix (left right : BitVec 64) : Nat → BitVec 128
  | 0 => 0
  | count + 1 => clmulPrefix left right count ^^^
      (if right.getLsbD count then left.setWidth 128 <<< count else 0)

/-- Complete polynomial product, before any modulus is applied. -/
def clmul128 (left right : BitVec 64) : BitVec 128 :=
  clmulPrefix left right 64

/-- Four-term polynomial multiple selected by a nibble's coefficients. -/
def nibbleMultiple (left : BitVec 64) (nibble : BitVec 4) : BitVec 128 :=
  clmulPrefix left (nibble.setWidth 64) 4

/-- GF(2) coefficient convolution. The guard avoids saturated Nat subtraction. -/
def clmulCoefficientPrefix (left right : BitVec 64) (index : Nat) : Nat → Bool
  | 0 => false
  | count + 1 => clmulCoefficientPrefix left right index count ^^
      (decide (count ≤ index) && left.getLsbD (index - count) && right.getLsbD count)

/-- Coefficient of X^index in the complete polynomial product. -/
def clmulCoefficient (left right : BitVec 64) (index : Nat) : Bool :=
  clmulCoefficientPrefix left right index 64

end BulksketchProofs.Field
