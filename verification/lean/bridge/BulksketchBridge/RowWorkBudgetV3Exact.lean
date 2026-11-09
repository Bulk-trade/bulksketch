import BulksketchBridge.RowWorkBudgetV3AllAccumulation
import BulksketchBridge.RowWorkBudgetV3AffineQuotes
import BulksketchBridge.RowWorkBudgetV3VerifierQuotes

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types
open AffineSelector (word word_val)

def v3U16Expected (capacity budget beta : Usize) (base : CostResult) : CostResult :=
  match base with
  | .Err error => .Err error
  | .Ok base =>
    let degree := core.cmp.impls.OrdUsize.min budget 18#usize
    let rank := degree.val - 1
    checkedCost (v3AdmittedUnits capacity budget degree base
      (word (originalVerifyUnits capacity.val beta.val))
      (word (rebuiltVerifyUnits capacity.val budget.val beta.val))
      (word (preparationUnits degree.val))
      (word (enumerationUnits degree.val rank))
      (word (splitterUnits degree.val rank)))

/-- The entire V3 wrapper for the admitted u16 capacity, budget and
    output dimensions. The V2 result is the original source callee;
    every V3 price quote and every cumulative check is derived. -/
def ActualNativeV3U16RowBound : Prop :=
  ∀ (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity budget beta candidates : Usize)
    (base : CostResult),
    capacity.val ≤ 65535 → budget.val ≤ 65535 → beta.val ≤ 65535 →
    WorkScheduleV2.row_bound sumCosts capacity budget beta candidates = .ok base →
    WorkScheduleV3.row_bound sumCosts capacity budget beta candidates =
      .ok (v3U16Expected capacity budget beta base)

theorem native_v3_u16_row_bound : ActualNativeV3U16RowBound := by
  intro sumCosts capacity budget beta candidates base capFit budgetFit betaFit priced
  cases base with
  | Err error =>
    exact (native_v3_prefix_exit sumCosts capacity budget beta candidates error).1 priced
  | Ok base =>
    let degree := core.cmp.impls.OrdUsize.min budget 18#usize
    let rank := ClosedLeafAdvance.usizeWord (degree.val - 1)
    let original := word (originalVerifyUnits capacity.val beta.val)
    let rebuilt := word (rebuiltVerifyUnits capacity.val budget.val beta.val)
    let setup := word (preparationUnits degree.val)
    let enumeration := word (enumerationUnits degree.val (degree.val - 1))
    let split := word (splitterUnits degree.val (degree.val - 1))
    have degreeMax : degree.val ≤ 18 := by
      simp only [degree, core.cmp.impls.OrdUsize.min_val, show (18#usize).val = 18 from rfl]
      exact Nat.min_le_right ..
    have platform : 18 ≤ Usize.max := by
      simp only [Usize.max, Usize.numBits, UScalarTy.numBits]
      rcases System.Platform.numBits_eq with width | width <;> rw [width] <;> decide
    have rankValue : rank.val = degree.val - 1 :=
      ClosedLeafAdvance.word_val _ ((Nat.sub_le ..).trans (degreeMax.trans platform))
    have rankMax : rank.val ≤ 17 := by rw [rankValue]; omega
    obtain ⟨verify, rebuild, verifyFit, _⟩ :=
      native_v3_verifier_quotes capacity budget beta capFit budgetFit betaFit
    obtain ⟨setupCall, enumCall, splitCall, affineFit⟩ :=
      native_v3_affine_quotes degree rank degreeMax rankMax
    rw [rankValue] at enumCall splitCall affineFit
    have originalValue : original.val = originalVerifyUnits capacity.val beta.val :=
      word_val _ (by omega)
    refine native_v3_all_accumulation sumCosts capacity budget beta candidates base original rebuilt setup enumeration split
      priced verify rebuild (fun _ => ⟨setupCall, enumCall, splitCall⟩) ?_ ?_ ?_ ?_
    · by_cases active : 3#usize ≤ degree
      · have degreeMin : 3 ≤ degree.val := by
          rw [UScalar.le_equiv] at active
          exact active
        have setupFits : preparationUnits degree.val ≤ U64.max := by omega
        have enumFits : enumerationUnits degree.val (degree.val - 1) ≤ U64.max := by
          exact (Nat.le_max_left ..).trans ((Nat.le_add_left ..).trans affineFit)
        have attemptPositive : 1 ≤ degree.val * (degree.val - 2) :=
          Nat.mul_le_mul (show 1 ≤ degree.val by omega) (show 1 ≤ degree.val - 2 by omega)
        have splitFits : splitterUnits degree.val (degree.val - 1) ≤ U64.max := by
          have raised := Nat.mul_le_mul_right (splitterUnits degree.val (degree.val - 1)) attemptPositive
          rw [Nat.one_mul] at raised
          exact raised.trans ((Nat.le_max_right ..).trans ((Nat.le_add_left ..).trans affineFit))
        change (if 3#usize ≤ degree then setup.val +
          max enumeration.val (degree.val * (degree.val - 2) * split.val) else 0) ≤ U64.max
        rw [ite_eq_left active, show setup.val = preparationUnits degree.val from word_val _ setupFits,
          show enumeration.val = enumerationUnits degree.val (degree.val - 1) from word_val _ enumFits,
          show split.val = splitterUnits degree.val (degree.val - 1) from word_val _ splitFits]
        exact affineFit
      · change (if 3#usize ≤ degree then setup.val +
          max enumeration.val (degree.val * (degree.val - 2) * split.val) else 0) ≤ U64.max
        rw [ite_eq_right active]
        exact Nat.zero_le _
    · change (if 3#usize ≤ capacity ∧ 3#usize ≤ budget then 863 + original.val else 0) ≤ U64.max
      split
      · rw [originalValue]
        omega
      · exact Nat.zero_le _
    · change (if 4#usize ≤ capacity ∧ 4#usize ≤ budget then 2337 + original.val else 0) ≤ U64.max
      split
      · rw [originalValue]
        omega
      · exact Nat.zero_le _
    · have three : budget.val / 3 ≤ 65535 := (Nat.div_le_self ..).trans budgetFit
      have four : budget.val / 4 ≤ 65535 := (Nat.div_le_self ..).trans budgetFit
      rw [U64.max_eq]
      omega

#print axioms native_v3_u16_row_bound

end BulksketchBridge.RootWorkBudget
