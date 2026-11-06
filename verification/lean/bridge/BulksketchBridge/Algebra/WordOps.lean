import BulksketchBridge.Algebra.Word

namespace BulksketchBridge.Algebra.Gf64

open Polynomial
open BulksketchProofs.Field
open scoped BigOperators


/-- Every prefix of carryless multiplication is exact polynomial convolution. -/
theorem wordPolynomial_clmulPrefix (left right : BitVec 64) (count : Nat)
    (bound : count ≤ 64) :
    wordPolynomial (clmulPrefix left right count) =
      wordPolynomial left *
        ∑ index ∈ Finset.range count, if right.getLsbD index then X ^ index else 0 := by
  induction count with
  | zero =>
    change wordPolynomial (0 : BitVec 128) = _
    rw [wordPolynomial_zero]
    simp
  | succ count inductionHypothesis =>
    rw [clmulPrefix, wordPolynomial_xor, inductionHypothesis (by omega),
      Finset.sum_range_succ, mul_add]
    apply congrArg (fun value => wordPolynomial left *
      (∑ index ∈ Finset.range count, if right.getLsbD index then X ^ index else 0) + value)
    cases right.getLsbD count
    · change wordPolynomial (0 : BitVec 128) = _
      rw [wordPolynomial_zero]
      simp
    · simp only [↓reduceIte]
      exact wordPolynomial_widen_shift left count (by omega)

/-- Complete multiplication is the ordinary product of the two coefficient polynomials. -/
theorem wordPolynomial_clmul (left right : BitVec 64) :
    wordPolynomial (clmul128 left right) = wordPolynomial left * wordPolynomial right :=
  wordPolynomial_clmulPrefix left right 64 (by decide)

/-- The bitvector modulus multiple is the exact polynomial multiple, with all
coefficients retained through degree 127. -/
theorem wordPolynomial_modulusMultiple (quotient : BitVec 64) :
    wordPolynomial (modulusMultiple128 quotient) = modulus * wordPolynomial quotient := by
  simp only [modulusMultiple128, fold128, wordPolynomial_xor,
    wordPolynomial_setWidth quotient (by decide : 64 ≤ 128),
    wordPolynomial_widen_shift quotient 64 (by decide),
    wordPolynomial_widen_shift quotient 1 (by decide),
    wordPolynomial_widen_shift quotient 3 (by decide),
    wordPolynomial_widen_shift quotient 4 (by decide), modulus]
  ring

/-- The native two-fold reduction has exactly the same class in Mathlib's
polynomial quotient, for every complete 128-bit input. -/
theorem toField_reduce (low high : BitVec 64) :
    toField (reduceFold64 low high) =
      AdjoinRoot.mk modulus (wordPolynomial (join128 low high)) := by
  rw [reduction_division_certificate, wordPolynomial_xor,
    wordPolynomial_setWidth _ (by decide : 64 ≤ 128),
    wordPolynomial_modulusMultiple, map_add, map_mul]
  have zero : AdjoinRoot.mk modulus modulus = 0 := AdjoinRoot.mk_self
  rw [zero, zero_mul, add_zero]
  rfl

/-- Native complete-word multiplication transports to the Mathlib field product. -/
theorem toField_mul (left right : BitVec 64) :
    toField (multiplyWord left right) = toField left * toField right := by
  rw [multiplyWord, toField_reduce, join128_split, wordPolynomial_clmul, map_mul]
  rfl

end BulksketchBridge.Algebra.Gf64
