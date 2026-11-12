import Arithmetic.RowWorkBudgetV2Generated
import BulksketchBridge.RowWorkBudgetV1

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-- Preserve the separately checked charge and accumulator additions. -/
def checkedBump (base verify : U64) (units : Nat) : CostResult :=
  match checkedCost (units + verify.val) with
  | .Err error => .Err error
  | .Ok extra => checkedCost (base.val + extra.val)

def v2Expected (capacity budget : Usize) (base verify : CostResult) : CostResult :=
  match base with
  | .Err error => .Err error
  | .Ok base =>
    match verify with
    | .Err error => .Err error
    | .Ok verify =>
      let first := if 1#usize ≤ budget then checkedBump base verify 1 else .Ok base
      match first with
      | .Err error => .Err error
      | .Ok first =>
        if 2#usize ≤ capacity ∧ 2#usize ≤ budget then checkedBump first verify 168 else .Ok first

def ActualNativeV2RowBound : Prop :=
  ∀ (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity budget beta candidates : Usize)
    (base verify : CostResult),
    WorkScheduleV1.row_bound sumCosts capacity budget beta candidates = .ok base →
    WorkScheduleV1.cost (.Verify capacity beta) = .ok verify →
    WorkScheduleV2.row_bound sumCosts capacity budget beta candidates = .ok (v2Expected capacity budget base verify)

private theorem addChecked (left right : U64) :
    add left right = .ok (checkedCost (left.val + right.val)) :=
  BmPrice.add_refines left right

theorem native_v2_row_bound : ActualNativeV2RowBound := by
  intro sumCosts capacity budget beta candidates base verify v1 checkedVerify
  cases base with
  | Err error =>
    simp only [WorkScheduleV2.row_bound, v1, v2Expected, bind_ok, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _
  | Ok base =>
    cases verify with
    | Err error =>
      simp only [WorkScheduleV2.row_bound, v1, v2Expected, checkedVerify, bind_ok, CoreOpsTry.branch,
        CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      exact bind_ok _ _
    | Ok verify =>
      have directOne : WorkScheduleV1.cost .DirectOne = .ok (.Ok 1#u64) := rfl
      have directTwo : WorkScheduleV1.cost .DirectTwo = .ok (.Ok 168#u64) := rfl
      by_cases first : 1#usize ≤ budget <;> by_cases cap : 2#usize ≤ capacity <;> by_cases size : 2#usize ≤ budget
      all_goals
        simp only [WorkScheduleV2.row_bound, v1, v2Expected, checkedVerify, bind_ok, CoreOpsTry.branch,
          first, cap, size, ite_true, ite_false, and_self, false_and, and_false,
          directOne, directTwo, checkedBump, addChecked,
          show (1#u64).val = 1 from rfl, show (168#u64).val = 168 from rfl]
        repeat' first
        | rfl
        | (split <;> simp_all only [bind_ok, CoreOpsTry.branch,
            CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            addChecked, show (1#u64).val = 1 from rfl, show (168#u64).val = 168 from rfl])
        | exact bind_ok _ _
        | assumption

#print axioms native_v2_row_bound

end BulksketchBridge.RootWorkBudget
