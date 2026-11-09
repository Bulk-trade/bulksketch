import BulksketchBridge.DenseDivisionAlgebra
import BulksketchBridge.Algebra.WordOps

namespace BulksketchBridge.Deflation

open Aeneas.Std Algebra.Gf64 SliceKernels Polynomial

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

def mulWord (left right : U64) : U64 := ⟨multiplyWord left.bv right.bv⟩

def remainderWord (locator quotient : Slice U64) (root : U64) : U64 :=
  locator[0]! ^^^ mulWord root quotient[0]!

/-- The completed source recurrence on the exact ascending coefficient
prefixes. The Rust loop fills quotient coefficients in reverse order. -/
structure SyntheticColumns (locator quotient : Slice U64) (root : U64) (degree : Nat) : Prop where
  positive : 0 < degree
  locatorLength : locator.length = degree + 1
  quotientLength : quotient.length = degree
  top : quotient[degree - 1]! = locator[degree]!
  prior : ∀ i, i + 1 < degree →
    quotient[i]! = locator[i + 1]! ^^^ mulWord root quotient[i + 1]!

private theorem xor_field (left right : U64) :
    toField (left ^^^ right).bv = toField left.bv + toField right.bv := toField_xor _ _

private theorem mul_field (left right : U64) :
    toField (mulWord left right).bv = toField left.bv * toField right.bv := toField_mul _ _

theorem remainder_field (locator quotient : Slice U64) (root : U64) :
    toField (remainderWord locator quotient root).bv =
      toField locator[0]!.bv + toField root.bv * toField quotient[0]!.bv := by
  rw [remainderWord, xor_field, mul_field]

/-- The reverse native arithmetic recurrence is synthetic division by the
linear root factor, with the computed constant as its exact remainder. -/
theorem synthetic_identity (locator quotient : Slice U64) (root : U64) (degree : Nat)
    (columns : SyntheticColumns locator quotient root degree) :
    slicePolynomial locator =
      (X + C (toField root.bv)) * slicePolynomial quotient +
        C (toField (remainderWord locator quotient root).bv) := by
  ext i
  rw [add_mul, coeff_add, coeff_add, coeff_C_mul]
  cases i with
  | zero =>
    rw [coeff_X_mul_zero, coeff_C_zero, zero_add, remainder_field]
    rw [slicePolynomial_coeff, slicePolynomial_coeff, ite_eq_left (by rw [columns.locatorLength]; omega),
      ite_eq_left (by rw [columns.quotientLength]; exact columns.positive)]
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  | succ i =>
    rw [coeff_X_mul, coeff_C_of_ne_zero (Nat.succ_ne_zero _), add_zero]
    have aLen := columns.locatorLength
    have qLen := columns.quotientLength
    rcases Nat.lt_trichotomy (i + 1) degree with lower | top | higher
    · rw [slicePolynomial_coeff, slicePolynomial_coeff, slicePolynomial_coeff,
        ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
        columns.prior i lower, xor_field, mul_field,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw [slicePolynomial_coeff, slicePolynomial_coeff, slicePolynomial_coeff,
        ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega), mul_zero, add_zero]
      have index : i = degree - 1 := by omega
      rw [top, index, columns.top]
    · rw [slicePolynomial_coeff, slicePolynomial_coeff, slicePolynomial_coeff,
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), mul_zero, add_zero]

theorem synthetic_remainder_eval (locator quotient : Slice U64) (root : U64) (degree : Nat)
    (columns : SyntheticColumns locator quotient root degree) :
    (slicePolynomial locator).eval (toField root.bv) =
      toField (remainderWord locator quotient root).bv := by
  rw [synthetic_identity locator quotient root degree columns]
  simp only [eval_add, eval_mul, eval_X, eval_C, CharTwo.add_self_eq_zero, zero_mul, zero_add]

theorem synthetic_remainder_zero_iff_root (locator quotient : Slice U64) (root : U64) (degree : Nat)
    (columns : SyntheticColumns locator quotient root degree) :
    remainderWord locator quotient root = 0#u64 ↔ (slicePolynomial locator).IsRoot (toField root.bv) := by
  unfold Polynomial.IsRoot
  rw [synthetic_remainder_eval locator quotient root degree columns]
  constructor
  · intro zero
    rw [zero]
    exact toField_zero
  · intro zero
    exact U64.bv_eq_imp_eq _ _ (toField_injective (zero.trans toField_zero.symm))

#print axioms synthetic_identity
#print axioms synthetic_remainder_zero_iff_root

end BulksketchBridge.Deflation
