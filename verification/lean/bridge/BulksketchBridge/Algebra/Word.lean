import BulksketchBridge.Algebra.WordSpec
import BulksketchProofs.Field.CLMul
import BulksketchProofs.Field.Reduction
import BulksketchProofs.Field.Period
import Mathlib.Algebra.CharP.Two

namespace BulksketchBridge.Algebra.Gf64

open Polynomial
open scoped BigOperators

/-- The polynomial interpretation preserves every coefficient, including zeros
past the word width. -/
theorem wordPolynomial_coeff {width : Nat} (input : BitVec width) (index : Nat) :
    (wordPolynomial input).coeff index = if input.getLsbD index then 1 else 0 := by
  classical
  rw [wordPolynomial, finsetSum_coeff]
  rw [Finset.sum_eq_single index]
  · cases input.getLsbD index <;> simp
  · intro other _ different
    cases input.getLsbD other <;> simp [coeff_X_pow, Ne.symm different]
  · intro absent
    have bit := BitVec.getLsbD_of_ge input index (by simpa using absent)
    simp [bit]

@[simp] theorem wordPolynomial_zero (width : Nat) :
    wordPolynomial (0 : BitVec width) = 0 := by
  ext index
  simp [wordPolynomial_coeff]

@[simp] theorem wordPolynomial_one {width : Nat} (positive : 0 < width) :
    wordPolynomial (1 : BitVec width) = 1 := by
  ext index
  rw [wordPolynomial_coeff]
  by_cases zero : index = 0
  · subst index
    simp [positive]
  · simp [coeff_one, zero]

theorem wordPolynomial_xor {width : Nat} (left right : BitVec width) :
    wordPolynomial (left ^^^ right) = wordPolynomial left + wordPolynomial right := by
  ext index
  simp only [wordPolynomial_coeff, coeff_add, BitVec.getLsbD_xor]
  cases left.getLsbD index <;> cases right.getLsbD index <;> decide

@[simp] theorem toField_zero : toField 0 = 0 := by
  change AdjoinRoot.mk modulus (wordPolynomial (0 : BitVec 64)) = 0
  rw [wordPolynomial_zero, map_zero]

@[simp] theorem toField_one : toField 1 = 1 := by
  change AdjoinRoot.mk modulus (wordPolynomial (1 : BitVec 64)) = 1
  rw [wordPolynomial_one (by decide : 0 < 64), map_one]

theorem toField_xor (left right : BitVec 64) :
    toField (left ^^^ right) = toField left + toField right := by
  simp [toField, wordPolynomial_xor]

/-- A nonzero word polynomial has degree strictly below its width. -/
theorem wordPolynomial_degree_lt {width : Nat} (input : BitVec width) :
    (wordPolynomial input).degree < width := by
  classical
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro index bound
  rw [wordPolynomial_coeff, BitVec.getLsbD_of_ge input index bound]
  rfl

theorem wordPolynomial_injective (width : Nat) :
    Function.Injective (wordPolynomial (width := width)) := by
  intro left right equal
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  have coefficient := congrArg (fun p : Polynomial (ZMod 2) => p.coeff index) equal
  rw [wordPolynomial_coeff, wordPolynomial_coeff] at coefficient
  cases hl : left.getLsbD index <;> cases hr : right.getLsbD index <;>
    simp only [hl, hr, Bool.false_eq_true, ↓reduceIte] at coefficient <;>
    simp_all only [zero_ne_one, one_ne_zero]

/-- Canonical representatives are unique in the monic degree-64 quotient. -/
theorem toField_injective : Function.Injective toField := by
  intro left right equal
  apply wordPolynomial_injective 64
  apply sub_eq_zero.mp
  by_contra nonzero
  have divides : modulus ∣ wordPolynomial left - wordPolynomial right :=
    AdjoinRoot.mk_eq_mk.mp equal
  have small : (wordPolynomial left - wordPolynomial right).degree < modulus.degree := by
    have target : modulus.degree = (64 : WithBot Nat) := by
      rw [degree_eq_natDegree modulus_monic.ne_zero, modulus_natDegree]
      rfl
    rw [target]
    exact (degree_sub_le _ _).trans_lt (max_lt (wordPolynomial_degree_lt left)
      (wordPolynomial_degree_lt right))
  exact (not_lt_of_ge (degree_le_of_dvd divides nonzero)) small

/-- Widening a coefficient word never changes its polynomial. -/
theorem wordPolynomial_setWidth {small large : Nat} (input : BitVec small)
    (bound : small ≤ large) :
    wordPolynomial (input.setWidth large) = wordPolynomial input := by
  ext index
  rw [wordPolynomial_coeff, wordPolynomial_coeff]
  by_cases inside : index < large
  · simp only [BitVec.getLsbD_setWidth, inside, decide_true, Bool.true_and]
  · have bit := BitVec.getLsbD_of_ge input index (by omega)
    simp only [BitVec.getLsbD_setWidth, inside, decide_false, Bool.false_and, bit]

/-- A bounded widening shift is exact multiplication by a monomial. -/
theorem wordPolynomial_widen_shift (input : BitVec 64) (count : Nat)
    (bound : count ≤ 64) :
    wordPolynomial (input.setWidth 128 <<< count) = wordPolynomial input * X ^ count := by
  ext index
  rw [wordPolynomial_coeff, coeff_mul_X_pow', wordPolynomial_coeff]
  by_cases inside : index < 128
  · by_cases before : index < count
    · simp [inside, before, show ¬count ≤ index by omega]
    · have atLeast : count ≤ index := by omega
      have subtraction : index - count < 128 := by omega
      simp [BitVec.getLsbD_shiftLeft, inside, before, atLeast, subtraction,
        -BitVec.getLsbD_eq_getElem]
  · have sourceBit := BitVec.getLsbD_of_ge input (index - count) (by omega)
    simp [BitVec.getLsbD_of_ge (input.setWidth 128 <<< count) index (by omega : 128 ≤ index), sourceBit]

end BulksketchBridge.Algebra.Gf64
