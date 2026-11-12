import BulksketchBridge.Algebra.Modulus
import Mathlib.RingTheory.AdjoinRoot
import BulksketchProofs.Field.CLMulSpec
import BulksketchProofs.Field.PeriodSpec

/-! Explicit polynomial-basis interpretation of the complete native word.
No field operation is supplied by the native implementation: the target is
Mathlib's quotient by the independently proved irreducible modulus. -/

namespace BulksketchBridge.Algebra.Gf64

open Polynomial
open scoped BigOperators

abbrev Field := AdjoinRoot modulus

instance modulusIrreducible : Fact (Irreducible modulus) := ⟨modulus_irreducible⟩

/-- All coefficient bits, with no truncation beyond the stated word width. -/
noncomputable def wordPolynomial {width : Nat} (input : BitVec width) :
    Polynomial (ZMod 2) :=
  ∑ index ∈ Finset.range width, if input.getLsbD index then X ^ index else 0

/-- The polynomial-basis map into the exact degree-64 Mathlib quotient field. -/
noncomputable def toField (input : BitVec 64) : Field :=
  AdjoinRoot.mk modulus (wordPolynomial input)

/-- The complete field multiplication word, before any source-language wrapper. -/
def multiplyWord (left right : BitVec 64) : BitVec 64 :=
  BulksketchProofs.Field.reduceFold64
    ((BulksketchProofs.Field.clmul128 left right).setWidth 64)
    (((BulksketchProofs.Field.clmul128 left right) >>> 64).setWidth 64)

end BulksketchBridge.Algebra.Gf64
