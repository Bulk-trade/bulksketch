import BulksketchBridge.ReconciliationLocatorSpec
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Vandermonde

/-! A consecutive power-sum recurrence is a weighted Vandermonde equation.
At positive start `s` its weights are `candidate.eval root`, with each root
contributing `root^s`. Starts `1` through the support size force these weights
to vanish since the roots are distinct and nonzero. -/

namespace BulksketchBridge.Reconciliation

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem supportLocator_monic (roots : Finset K) : (supportLocator roots).Monic :=
  Polynomial.monic_prod_X_sub_C id roots

theorem supportLocator_natDegree (roots : Finset K) :
    (supportLocator roots).natDegree = roots.card :=
  Polynomial.natDegree_finsetProd_X_sub_C_eq_card roots id

/-- Expanding each observed power sum gives a weighted evaluation of the
recurrence polynomial at the support. -/
theorem recurrence_sum_eq_weighted_eval (roots : Finset K) (candidate : Polynomial K)
    (start : Nat) :
    positiveRecurrenceSum roots candidate start =
      ∑ root ∈ roots, candidate.eval root * root ^ start := by
  simp only [positiveRecurrenceSum, powerSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro root _
  rw [eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro term _
  rw [pow_add, mul_comm (root ^ start) (root ^ term), mul_assoc]

/-- The support locator gives a recurrence for every start and prefix length. -/
theorem supportLocator_recurs (roots : Finset K) (observed : Nat) :
    positiveRecurrenceThrough roots (supportLocator roots) observed := by
  intro start _ _
  rw [recurrence_sum_eq_weighted_eval]
  apply Finset.sum_eq_zero
  intro root member
  have evalZero : (supportLocator roots).eval root = 0 := by
    rw [supportLocator, eval_prod]
    apply Finset.prod_eq_zero member
    simp
  rw [evalZero, zero_mul]

/-- The first `roots.card` positive recurrence starts determine all support
root evaluations. The zeroth Vandermonde column is shifted by incorporating
one factor of each root into its weight. -/
theorem eval_zero_of_positive_recurrence (roots : Finset K) (candidate : Polynomial K)
    (observed : Nat) (noZero : (0 : K) ∉ roots)
    (enough : roots.card + candidate.natDegree ≤ observed)
    (recurs : positiveRecurrenceThrough roots candidate observed) :
    ∀ root ∈ roots, candidate.eval root = 0 := by
  classical
  let enumerate := roots.equivFin.symm
  let values : Fin roots.card → K := fun index => (enumerate index).val
  have distinct : Function.Injective values :=
    Subtype.val_injective.comp enumerate.injective
  have vanishes (index : Fin roots.card) :
      (∑ rootIndex : Fin roots.card,
        (candidate.eval (values rootIndex) * values rootIndex) *
          values rootIndex ^ (index : Nat)) = 0 := by
    simp_rw [mul_assoc, ← pow_succ']
    change (∑ rootIndex,
      (fun root : roots => candidate.eval root.val * root.val ^ ((index : Nat) + 1))
        (enumerate rootIndex)) = 0
    rw [Equiv.sum_comp enumerate
        (fun root : roots => candidate.eval root.val * root.val ^ ((index : Nat) + 1)),
      Finset.sum_coe_sort roots (fun root : K => candidate.eval root * root ^ ((index : Nat) + 1)),
      ← recurrence_sum_eq_weighted_eval]
    exact recurs ((index : Nat) + 1) (Nat.succ_pos _)
      ((Nat.add_le_add_right index.isLt candidate.natDegree).trans enough)
  have weightsZero : (fun index => candidate.eval (values index) * values index) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero distinct vanishes
  intro root member
  have zeroProduct : candidate.eval root * root = 0 := by
    simpa [values, enumerate] using congrFun weightsZero (roots.equivFin ⟨root, member⟩)
  exact (mul_eq_zero.mp zeroProduct).resolve_right (fun zero => noZero (zero ▸ member))

/-- Distinct support roots give a product divisor of every nonzero recurrence
polynomial that fits enough consecutive positive moments. -/
theorem supportLocator_dvd_of_positive_recurrence (roots : Finset K)
    (candidate : Polynomial K) (observed : Nat) (noZero : (0 : K) ∉ roots)
    (nonzero : candidate ≠ 0) (enough : roots.card + candidate.natDegree ≤ observed)
    (recurs : positiveRecurrenceThrough roots candidate observed) :
    supportLocator roots ∣ candidate := by
  change (roots.val.map (fun root => X - C root)).prod ∣ candidate
  apply (Multiset.prod_X_sub_C_dvd_iff_le_roots nonzero roots.val).mpr
  apply Finset.val_le_iff_val_subset.mpr
  intro root member
  exact (Polynomial.mem_roots nonzero).mpr
    (eval_zero_of_positive_recurrence roots candidate observed noZero enough recurs root member)

/-- Minimal degree follows from divisibility by the support locator. -/
theorem positive_locator_minimal (roots : Finset K) (candidate : Polynomial K)
    (observed : Nat) (noZero : (0 : K) ∉ roots) (nonzero : candidate ≠ 0)
    (enough : roots.card + candidate.natDegree ≤ observed)
    (recurs : positiveRecurrenceThrough roots candidate observed) :
    supportLocator roots ∣ candidate ∧ roots.card ≤ candidate.natDegree := by
  have divides := supportLocator_dvd_of_positive_recurrence roots candidate observed
    noZero nonzero enough recurs
  exact ⟨divides, supportLocator_natDegree roots ▸ Polynomial.natDegree_le_of_dvd divides nonzero⟩

/-- Monicity fixes the scaling, so the unique smallest-degree polynomial is the
product of the linear support factors. -/
theorem positive_locator_unique (roots : Finset K) (candidate : Polynomial K)
    (observed : Nat) (noZero : (0 : K) ∉ roots) (monic : candidate.Monic)
    (small : candidate.natDegree ≤ roots.card)
    (enough : roots.card + candidate.natDegree ≤ observed)
    (recurs : positiveRecurrenceThrough roots candidate observed) :
    candidate = supportLocator roots := by
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (supportLocator_monic roots) monic
  · exact supportLocator_dvd_of_positive_recurrence roots candidate observed
      noZero monic.ne_zero enough recurs
  · rw [supportLocator_natDegree]
    exact small

theorem gf64_positive_locator_minimal : GF64PositiveLocatorMinimal := positive_locator_minimal

theorem gf64_positive_locator_unique : GF64PositiveLocatorUnique := positive_locator_unique

end BulksketchBridge.Reconciliation
