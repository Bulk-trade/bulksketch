import BulksketchBridge.RowWorkBudgetV3Prefix

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts

set_option maxRecDepth 4096

/-- The first V3 verifier reserve addition has its original checked
    overflow exit after the exact safe max-minus-original subtraction. -/
def ActualNativeV3VerifierReserveExit : Prop :=
  ∀ (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity budget beta candidates : Usize)
    (base original rebuilt : U64),
    WorkScheduleV2.row_bound sumCosts capacity budget beta candidates = .ok (.Ok base) →
    WorkScheduleV1.cost (.Verify capacity beta) = .ok (.Ok original) →
    WorkScheduleV1.cost (.VerifyLfsr capacity beta budget) = .ok (.Ok rebuilt) →
    U64.max < base.val + (max rebuilt.val original.val - original.val) →
    WorkScheduleV3.row_bound sumCosts capacity budget beta candidates = .ok (.Err .WorkLimitExceeded)

theorem native_v3_verifier_reserve_exit : ActualNativeV3VerifierReserveExit := by
  intro sumCosts capacity budget beta candidates base original rebuilt v2 verify rebuilding overflow
  let high := core.cmp.impls.OrdU64.max rebuilt original
  have highValue : high.val = max rebuilt.val original.val :=
    core.cmp.impls.OrdU64.max_val rebuilt original
  obtain ⟨extra, subtract, extraValue, _⟩ := RawMulTable.normal_of_spec _ _
    (U64.sub_spec (x := high) (y := original) (by rw [highValue]; exact Nat.le_max_right ..))
  have rejected : add base extra = .ok (.Err .WorkLimitExceeded) := by
    rw [BmPrice.add_refines, extraValue, highValue, checkedCost, dite_eq_right (Nat.not_le_of_gt overflow)]
  dsimp only [high] at subtract
  simp only [WorkScheduleV3.row_bound, v2, verify, rebuilding, lift, bind_ok, CoreOpsTry.branch,
    subtract, rejected, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  exact bind_ok _ _

#print axioms native_v3_verifier_reserve_exit

end BulksketchBridge.RootWorkBudget
