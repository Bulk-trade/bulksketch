import BulksketchBridge.SlicePolynomial

namespace BulksketchBridge.DenseMul

open Aeneas.Std BulksketchBridge.Algebra.Gf64 SliceKernels Polynomial
open scoped BigOperators

noncomputable def contribution (a b : Slice U64) (left slot : Nat) : Field :=
  if left ≤ slot ∧ slot - left < b.length then
    toField a[left]!.bv * toField b[slot - left]!.bv
  else 0

/-- A fixed output coefficient of the ascending product. Terms whose
right index falls outside the input are absent. -/
theorem coeff_product (a b : Slice U64) (slot : Nat) :
    (slicePolynomial a * slicePolynomial b).coeff slot =
      ∑ left ∈ Finset.range a.length, contribution a b left slot := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  let stop := min (slot + 1) a.length
  calc
    _ = ∑ left ∈ Finset.range stop,
          (slicePolynomial a).coeff left * (slicePolynomial b).coeff (slot - left) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.min_le_left _ _))
      intro left inSlot outside
      have tooLarge : ¬ left < a.length := by
        simp only [Finset.mem_range, stop] at inSlot outside
        omega
      rw [slicePolynomial_coeff, ite_eq_right tooLarge, zero_mul]
    _ = ∑ left ∈ Finset.range stop, contribution a b left slot := by
      apply Finset.sum_congr rfl
      intro left inStop
      simp only [Finset.mem_range, stop] at inStop
      have leftBound : left < a.length := by omega
      have leftLe : left ≤ slot := by omega
      rw [slicePolynomial_coeff, slicePolynomial_coeff, ite_eq_left leftBound]
      by_cases rightBound : slot - left < b.length
      · simp [contribution, leftLe, rightBound]
      · simp [contribution, rightBound]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (Nat.min_le_right _ _))
      intro left inSource outside
      have tooLarge : ¬ left ≤ slot := by
        simp only [Finset.mem_range, stop] at inSource outside
        omega
      simp [contribution, tooLarge]

theorem coeff_product_outside (a b : Slice U64) (slot : Nat)
    (outside : a.length + b.length - 1 ≤ slot) :
    (slicePolynomial a * slicePolynomial b).coeff slot = 0 := by
  rw [coeff_product]
  apply Finset.sum_eq_zero
  intro left inSource
  have leftBound := Finset.mem_range.mp inSource
  have absent : ¬ (left ≤ slot ∧ slot - left < b.length) := by omega
  simp [contribution, absent]

end BulksketchBridge.DenseMul
