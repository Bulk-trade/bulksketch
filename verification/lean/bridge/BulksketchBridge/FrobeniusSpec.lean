import Aeneas
import BulksketchProofs.Field.ReductionSpec
import BulksketchProofs.Field.SpreadSpec

/-!
Frozen word-level specification for native portable GF64 repeated squaring.
The recurrence uses independent complete-bit polynomial-square/remainder models.
The source reduces the requested U32 power modulo 64 before iterating. This
specification preserves that behavior for every input and every U32 power.
It does not assert that applying square 64 times is the identity: that separate
algebraic period theorem needs an independently checked modulus certificate.
-/

namespace BulksketchBridge.Frobenius

open Aeneas.Std

/-- One complete polynomial square reduced by the native modulus. -/
def squareBits (input : BitVec 64) : BitVec 64 :=
  BulksketchProofs.Field.reduceFold64
    (BulksketchProofs.Field.spread64 input)
    (BulksketchProofs.Field.spread64 (input >>> 32))

/-- Exact iteration count, with no field-period assumption. -/
def repeatedSquare : Nat → BitVec 64 → BitVec 64
  | 0, input => input
  | Nat.succ count, input => squareBits (repeatedSquare count input)

/-- The source requests between zero and 63 squarings, inclusive. -/
def expectedWord (input : U64) (power : U32) : U64 :=
  ⟨repeatedSquare (power.val % 64) input.bv⟩

end BulksketchBridge.Frobenius
