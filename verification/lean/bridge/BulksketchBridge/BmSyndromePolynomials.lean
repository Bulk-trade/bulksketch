import BulksketchBridge.BmParity
import BulksketchBridge.ReconstructionPowerSums

namespace BulksketchBridge.BmSyndromePolynomials

open Polynomial Aeneas.Std Algebra.Gf64
open scoped BigOperators

set_option maxRecDepth 4096

noncomputable def boundedPolynomial (values : Nat → Field) (size : Nat) : Polynomial Field :=
  ∑ i ∈ Finset.range size, monomial i (values i)

theorem coeff_boundedPolynomial (values : Nat → Field) (size i : Nat) :
    (boundedPolynomial values size).coeff i = if i < size then values i else 0 := by
  classical
  unfold boundedPolynomial
  rw [finsetSum_coeff]
  by_cases h : i < size
  · rw [ite_eq_left h, Finset.sum_eq_single i]
    · simp
    · intro j _ distinct
      simp [coeff_monomial, distinct]
    · intro absent
      exact (absent (Finset.mem_range.mpr h)).elim
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro j member
    have distinct : j ≠ i := by
      have := Finset.mem_range.mp member
      omega
    simp [coeff_monomial, distinct]

noncomputable def connectionPolynomial (connection : Slice U64) (degree : Nat) :
    Polynomial Field :=
  boundedPolynomial (fun i => toField connection[i]!.bv) (degree + 1)

noncomputable def syndromePolynomial (syndromes : Slice U64) : Polynomial Field :=
  boundedPolynomial (fun i => if i = 0 then 0 else toField syndromes[i]!.bv) syndromes.length

theorem syndrome_coeff_zero (syndromes : Slice U64) : (syndromePolynomial syndromes).coeff 0 = 0 := by
  simp [syndromePolynomial, coeff_boundedPolynomial]

theorem discrepancy_polynomial (connection syndromes : Slice U64) (degree m : Nat)
    (before : degree < m) (syndromeBound : m < syndromes.length) :
    (connectionPolynomial connection degree * syndromePolynomial syndromes).coeff m =
      ∑ i ∈ Finset.range (degree + 1), toField connection[i]!.bv * toField syndromes[m - i]!.bv := by
  classical
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [connectionPolynomial, syndromePolynomial, coeff_boundedPolynomial]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show degree + 1 ≤ m + 1 by omega))]
  · apply Finset.sum_congr rfl
    intro i member
    have bounded := Finset.mem_range.mp member
    simp [bounded, show m - i < syndromes.length by omega, show m - i ≠ 0 by omega]
  · intro i _ outside
    have unbounded : ¬ i < degree + 1 := fun h => outside (Finset.mem_range.mpr h)
    simp [unbounded]

theorem connection_degree (connection : Slice U64) (degree : Nat) :
    (connectionPolynomial connection degree).natDegree ≤ degree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i above
  simp [connectionPolynomial, coeff_boundedPolynomial, show ¬ i < degree + 1 by omega]

theorem reconstruction_square (difference initial syndromes : Slice U64) (processed power : Nat)
    (reconstructed : Reconstruction.Prefix difference initial syndromes processed)
    (valid : 2 * power < processed) (bound : 2 * power < syndromes.length) :
    (syndromePolynomial syndromes).coeff (2 * power) =
      ((syndromePolynomial syndromes).coeff power) ^ 2 := by
  by_cases initialPower : power = 0
  · simp [initialPower, syndrome_coeff_zero]
  have positive : 0 < 2 * power := by omega
  have recurrence := reconstructed.recurrence (2 * power) positive valid
  have even : (2 * power) % 2 = 0 := by omega
  have half : 2 * power / 2 = power := by omega
  simp only [Reconstruction.SyndromeStep, even, ite_true, half] at recurrence
  have castValue := congrArg (fun word : U64 => toField word.bv) recurrence
  change toField syndromes.val[2 * power]!.bv =
    toField (BulksketchProofs.Field.Period.squareWord syndromes.val[power]!.bv) at castValue
  rw [toField_square] at castValue
  have doubledNZ : 2 * power ≠ 0 := by omega
  have halfBound : power < syndromes.length := by omega
  simp only [syndromePolynomial, coeff_boundedPolynomial, bound, halfBound, doubledNZ, initialPower,
    ite_true, ite_false]
  simpa only [Slice.getElem!_Nat_eq] using castValue

/-- The dot product skipped by the native odd-index branch is zero under
the established residual prefix and original reconstruction contract. -/
theorem reconstructed_skip (connection difference initial syndromes : Slice U64)
    (degree power processed : Nat) (degreeBound : degree < power)
    (even : power % 2 = 0) (processedBound : power < processed)
    (syndromeBound : power < syndromes.length)
    (reconstructed : Reconstruction.Prefix difference initial syndromes processed)
    (earlier : ∀ i < power,
      (BmParity.residual (connectionPolynomial connection degree) (syndromePolynomial syndromes)).coeff i = 0) :
    ∑ i ∈ Finset.range (degree + 1), toField connection[i]!.bv * toField syndromes[power - i]!.bv = 0 := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  rw [← discrepancy_polynomial connection syndromes degree power degreeBound syndromeBound]
  apply BmParity.skipped_discrepancy _ _ power even (syndrome_coeff_zero syndromes) _ earlier
  intro i bounded
  exact reconstruction_square difference initial syndromes processed i reconstructed (by omega) (by omega)

end BulksketchBridge.BmSyndromePolynomials
