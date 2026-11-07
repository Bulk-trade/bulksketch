import BulksketchBridge.ReconciliationLfsrSpec
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Each root contributes the sequence `r * (r²)^index`. Evaluation of the
squared-coefficient locator at the inverse squared root gives zero. Scaling
that identity by `r^(2*index+1)` gives the native lag order. -/

namespace BulksketchBridge.Reconciliation

open Polynomial
open scoped BigOperators

section BinaryField

variable {K : Type*} [Field K]

theorem rebuiltLocator_degree_le (roots : Finset K) :
    (rebuiltLocator roots).natDegree ≤ roots.card := by
  unfold rebuiltLocator
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ root ∈ roots, (1 + C root * X).natDegree ≤ ∑ _root ∈ roots, (1 : Nat) := by
      apply Finset.sum_le_sum
      intro root _
      apply (Polynomial.natDegree_add_le _ _).trans
      simp only [natDegree_one, Nat.zero_max]
      simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le root 1
    _ = roots.card := by simp

theorem rebuiltLocator_constant (roots : Finset K) :
    (rebuiltLocator roots).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, rebuiltLocator, eval_prod]
  simp

private theorem cancel_lag_power (root : K) (nonzero : root ≠ 0) (index lag : Nat)
    (bounded : lag ≤ index) :
    root ^ (2 * index + 1) * ((root⁻¹) ^ 2) ^ lag = root ^ (2 * (index - lag) + 1) := by
  rw [← pow_mul, inv_pow,
    show 2 * index + 1 = (2 * (index - lag) + 1) + 2 * lag by omega,
    pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ nonzero), mul_one]

variable [CharP K 2]

private theorem rebuiltLocator_eval_inverse_zero (roots : Finset K) (root : K)
    (member : root ∈ roots) (nonzero : root ≠ 0) :
    (rebuiltLocator roots).eval root⁻¹ = 0 := by
  rw [rebuiltLocator, eval_prod]
  apply Finset.prod_eq_zero member
  simp only [eval_add, eval_one, eval_mul, eval_C, eval_X, mul_inv_cancel₀ nonzero]
  exact CharTwo.add_self_eq_zero 1

private theorem squared_locator_eval_sum_zero (roots : Finset K) (root : K)
    (member : root ∈ roots) (nonzero : root ≠ 0) :
    (∑ lag ∈ Finset.range (roots.card + 1),
      (rebuiltLocator roots).coeff lag ^ 2 * ((root⁻¹) ^ 2) ^ lag) = 0 := by
  have bounded : ((rebuiltLocator roots).map (frobenius K 2)).natDegree < roots.card + 1 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans (rebuiltLocator_degree_le roots))
  have zeroEvaluation :
      ((rebuiltLocator roots).map (frobenius K 2)).eval ((root⁻¹) ^ 2) = 0 := by
    change ((rebuiltLocator roots).map (frobenius K 2)).eval (frobenius K 2 root⁻¹) = 0
    rw [eval_map_apply, rebuiltLocator_eval_inverse_zero roots root member nonzero, map_zero]
  rw [eval_eq_sum_range' bounded] at zeroEvaluation
  simpa only [coeff_map, frobenius_def] using zeroEvaluation

/-- Odd moments of the support obey the recurrence derived from its rebuilt
locator. Degree zero is included through the empty sums. -/
theorem rebuilt_odd_recurrence (roots : Finset K) (noZero : (0 : K) ∉ roots)
    (index : Nat) (bounded : roots.card ≤ index) :
    oddSyndrome roots index = oddContinuation (rebuiltLocator roots) roots.card
      (oddSyndrome roots) index := by
  have homogeneous :
      (∑ lag ∈ Finset.range (roots.card + 1),
        (rebuiltLocator roots).coeff lag ^ 2 * oddSyndrome roots (index - lag)) = 0 := by
    simp only [oddSyndrome, powerSum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro root member
    have nonzero : root ≠ 0 := fun zero => noZero (zero ▸ member)
    calc
      (∑ lag ∈ Finset.range (roots.card + 1),
          (rebuiltLocator roots).coeff lag ^ 2 * root ^ (2 * (index - lag) + 1)) =
        root ^ (2 * index + 1) * ∑ lag ∈ Finset.range (roots.card + 1),
          (rebuiltLocator roots).coeff lag ^ 2 * ((root⁻¹) ^ 2) ^ lag := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro lag inside
            have lagBound : lag ≤ index := by
              have := Finset.mem_range.mp inside
              omega
            rw [mul_left_comm, ← cancel_lag_power root nonzero index lag lagBound]
      _ = 0 := by rw [squared_locator_eval_sum_zero roots root member nonzero, mul_zero]
  rw [Finset.sum_range_succ'] at homogeneous
  exact (CharTwo.add_eq_zero.mp (by
    simpa only [rebuiltLocator_constant, one_pow, one_mul, Nat.sub_zero,
      oddContinuation] using homogeneous)).symm

end BinaryField

section Continuation

variable {K : Type*} [CommSemiring K]

/-- Every continuation coefficient multiplies a strictly earlier entry. -/
theorem oddContinuation_congr (locator : Polynomial K) (degree index : Nat)
    (bounded : degree ≤ index) (left right : Nat → K)
    (sameEarlier : ∀ earlier, earlier < index → left earlier = right earlier) :
    oddContinuation locator degree left index = oddContinuation locator degree right index := by
  apply Finset.sum_congr rfl
  intro offset inside
  have := Finset.mem_range.mp inside
  rw [sameEarlier _ (by omega)]

/-- A checked seed plus all continuation equations fixes every word in the
prefix, provided the reference row satisfies those same equations. -/
theorem prefix_continuation_iff_full (locator : Polynomial K) (degree capacity : Nat)
    (reference row : Nat → K)
    (referenceRecurrence : ∀ index, degree ≤ index →
      reference index = oddContinuation locator degree reference index) :
    ((∀ index, index < min degree capacity → row index = reference index) ∧
      (∀ index, degree ≤ index → index < capacity →
        row index = oddContinuation locator degree row index)) ↔
    (∀ index, index < capacity → row index = reference index) := by
  constructor
  · rintro ⟨seed, continuation⟩ index inside
    induction index using Nat.strong_induction_on with
    | h index inductionHypothesis =>
      by_cases seedIndex : index < degree
      · exact seed index (lt_min seedIndex inside)
      · have continued : degree ≤ index := Nat.le_of_not_gt seedIndex
        calc
          row index = oddContinuation locator degree row index :=
            continuation index continued inside
          _ = oddContinuation locator degree reference index :=
            oddContinuation_congr locator degree index continued row reference
              (fun earlier before => inductionHypothesis earlier before (before.trans inside))
          _ = reference index := (referenceRecurrence index continued).symm
  · intro full
    constructor
    · intro index inside
      exact full index (inside.trans_le (Nat.min_le_right _ _))
    · intro index continued inside
      calc
        row index = reference index := full index inside
        _ = oddContinuation locator degree reference index := referenceRecurrence index continued
        _ = oddContinuation locator degree row index :=
          oddContinuation_congr locator degree index continued reference row
            (fun earlier before => (full earlier (before.trans inside)).symm)

end Continuation

open Algebra.Gf64

theorem gf64_rebuilt_locator_recurrence : GF64RebuiltLocatorRecurrence := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  exact rebuilt_odd_recurrence

theorem gf64_rebuilt_verification_iff_direct : GF64RebuiltVerificationIffDirect := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  intro roots row capacity noZero
  exact prefix_continuation_iff_full (rebuiltLocator roots) roots.card capacity
    (oddSyndrome roots) row (rebuilt_odd_recurrence roots noZero)

end BulksketchBridge.Reconciliation
