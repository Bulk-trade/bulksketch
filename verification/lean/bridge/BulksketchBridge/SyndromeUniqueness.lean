import BulksketchBridge.SyndromeUniquenessSpec
import BulksketchBridge.Algebra.Word
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Finset.SymmDiff
import Mathlib.LinearAlgebra.Vandermonde

/-! A Vandermonde argument gives an unconditional uniqueness theorem for
bounded distinct supports. It also gives a separate identity for reconstructing
the positive even power sums by squaring. -/

namespace BulksketchBridge.Reconciliation

open scoped BigOperators symmDiff

section Field

variable {K : Type*} [Field K]

/-- The first `roots.card` positive power sums of a nonzero support cannot
all vanish unless the support is empty. The Vandermonde matrix has powers
starting at zero, so its coefficient vector consists of the roots themselves. -/
theorem eq_empty_of_positive_powerSums_zero (roots : Finset K)
    (noZero : (0 : K) ∉ roots)
    (zeroSums : ∀ power, 0 < power → power ≤ roots.card → powerSum roots power = 0) :
    roots = ∅ := by
  classical
  let enumerate := roots.equivFin.symm
  let values : Fin roots.card → K := fun index => (enumerate index).val
  have distinct : Function.Injective values :=
    Subtype.val_injective.comp enumerate.injective
  have vanishes (index : Fin roots.card) :
      (∑ rootIndex : Fin roots.card, values rootIndex * values rootIndex ^ (index : Nat)) = 0 := by
    simp_rw [← pow_succ']
    change (∑ rootIndex, (enumerate rootIndex).val ^ ((index : Nat) + 1)) = 0
    rw [Equiv.sum_comp enumerate (fun root : roots => root.val ^ ((index : Nat) + 1)),
      Finset.sum_coe_sort roots (fun root : K => root ^ ((index : Nat) + 1))]
    exact zeroSums ((index : Nat) + 1) (Nat.succ_pos _) index.isLt
  have allZero : values = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero distinct vanishes
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro root member
  have rootZero : root = 0 := by
    simpa [values, enumerate] using congrFun allZero (roots.equivFin ⟨root, member⟩)
  exact noZero (rootZero ▸ member)

end Field

section BinaryField

variable {K : Type*} [Field K] [CharP K 2]

/-- Squaring a power sum doubles its power in characteristic two. -/
theorem powerSum_even (roots : Finset K) (power : Nat) :
    powerSum roots (power * 2) = powerSum roots power ^ 2 := by
  simp only [powerSum, pow_mul]
  exact (sum_pow_char 2 roots (fun root => root ^ power)).symm

/-- The checked odd prefix determines the whole positive syndrome prefix. -/
theorem positive_powerSums_eq_of_oddSyndromes_eq (capacity : Nat)
    (left right : Finset K)
    (same : ∀ index, index < capacity → oddSyndrome left index = oddSyndrome right index)
    (power : Nat) (positive : 0 < power) (bounded : power ≤ 2 * capacity) :
    powerSum left power = powerSum right power := by
  induction power using Nat.strong_induction_on with
  | h power inductionHypothesis =>
    by_cases odd : power % 2 = 1
    · have oddPower : power = 2 * (power / 2) + 1 := by omega
      have checked : power / 2 < capacity := by omega
      rw [oddPower]
      exact same (power / 2) checked
    · have evenPower : power = (power / 2) * 2 := by omega
      have smaller : power / 2 < power := by omega
      have halfPositive : 0 < power / 2 := by omega
      have halfBounded : power / 2 ≤ 2 * capacity := by omega
      rw [evenPower, powerSum_even, powerSum_even,
        inductionHypothesis (power / 2) smaller halfPositive halfBounded]

/-- A common root contributes twice and cancels. -/
theorem powerSum_symmDiff [DecidableEq K] (left right : Finset K) (power : Nat) :
    powerSum (left ∆ right) power = powerSum left power + powerSum right power := by
  simp only [powerSum, symmDiff_eq_sup_sdiff_inf, Finset.sup_eq_union, Finset.inf_eq_inter]
  rw [eq_sub_of_add_eq (Finset.sum_sdiff (f := fun root => root ^ power)
    (show left ∩ right ⊆ left ∪ right from
      Finset.inter_subset_left.trans Finset.subset_union_left)),
    CharTwo.sub_eq_add, Finset.sum_union_inter]

/-- More generally it is enough to bound the symmetric difference by twice
the number of checked odd syndromes. -/
theorem eq_of_oddSyndromes_eq_of_symmDiff_card_le [DecidableEq K] (capacity : Nat)
    (left right : Finset K) (bounded : (left ∆ right).card ≤ 2 * capacity)
    (noZero : (0 : K) ∉ left ∆ right)
    (same : ∀ index, index < capacity → oddSyndrome left index = oddSyndrome right index) :
    left = right := by
  apply Finset.symmDiff_eq_empty.mp
  apply eq_empty_of_positive_powerSums_zero _ noZero
  intro power positive small
  have equal := positive_powerSums_eq_of_oddSyndromes_eq capacity left right same
    power positive (small.trans bounded)
  rw [powerSum_symmDiff, equal, CharTwo.add_self_eq_zero]

/-- On distinct nonzero supports of size at most capacity, the stored odd
power sums are injective. -/
theorem eq_of_oddSyndromes_eq (capacity : Nat) (left right : Finset K)
    (leftBounded : left.card ≤ capacity) (rightBounded : right.card ≤ capacity)
    (leftNoZero : (0 : K) ∉ left) (rightNoZero : (0 : K) ∉ right)
    (same : ∀ index, index < capacity → oddSyndrome left index = oddSyndrome right index) :
    left = right := by
  classical
  apply eq_of_oddSyndromes_eq_of_symmDiff_card_le capacity left right _ _ same
  · have bound := (Finset.card_le_card Finset.symmDiff_subset_union).trans
      (Finset.card_union_le left right)
    omega
  · simp [Finset.mem_symmDiff, leftNoZero, rightNoZero]

end BinaryField

open Algebra.Gf64

private noncomputable def fieldEmbedding : BitVec 64 ↪ Field :=
  ⟨toField, toField_injective⟩

private theorem wordPowerSum_eq (roots : Finset (BitVec 64)) (power : Nat) :
    powerSum (roots.map fieldEmbedding) power = wordPowerSum roots power :=
  Finset.sum_map roots fieldEmbedding (fun root => root ^ power)

theorem gf64_positive_powerSums : GF64OddSyndromesDeterminePositivePowers := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  intro capacity left right same power positive bounded
  rw [← wordPowerSum_eq, ← wordPowerSum_eq]
  apply positive_powerSums_eq_of_oddSyndromes_eq capacity _ _ _ power positive bounded
  intro index checked
  simpa only [oddSyndrome, wordPowerSum_eq, wordOddSyndrome] using same index checked

theorem gf64_sparse_support_unique : GF64OddSyndromesIdentifySparseSupport := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  intro capacity left right leftBounded rightBounded leftNoZero rightNoZero same
  apply Finset.map_injective fieldEmbedding
  apply eq_of_oddSyndromes_eq capacity _ _
  · simpa only [Finset.card_map] using leftBounded
  · simpa only [Finset.card_map] using rightBounded
  · intro member
    obtain ⟨word, inLeft, zero⟩ := Finset.mem_map.mp member
    have wordZero : word = 0 := toField_injective (zero.trans toField_zero.symm)
    exact leftNoZero (wordZero ▸ inLeft)
  · intro member
    obtain ⟨word, inRight, zero⟩ := Finset.mem_map.mp member
    have wordZero : word = 0 := toField_injective (zero.trans toField_zero.symm)
    exact rightNoZero (wordZero ▸ inRight)
  · intro index checked
    simpa only [oddSyndrome, wordPowerSum_eq, wordOddSyndrome] using same index checked

end BulksketchBridge.Reconciliation
