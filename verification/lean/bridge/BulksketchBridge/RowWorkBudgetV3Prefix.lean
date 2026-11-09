import Arithmetic.RowWorkBudgetV3Generated
import BulksketchBridge.MaxAffineDegree
import BulksketchBridge.BmPrice
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts

set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

/-- The original V3 wrapper preserves the exact first error before
    the affine and closed-form reserve branches. -/
def ActualNativeV3PrefixExit : Prop :=
  ∀ (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity budget beta candidates : Usize) (error : DecodeError),
    let source := WorkScheduleV3.row_bound sumCosts capacity budget beta candidates
    let v2 := WorkScheduleV2.row_bound sumCosts capacity budget beta candidates
    let verify := WorkScheduleV1.cost (.Verify capacity beta)
    let rebuilt := WorkScheduleV1.cost (.VerifyLfsr capacity beta budget)
    (v2 = .ok (.Err error) →
      source = .ok (.Err error)) ∧
    (∀ base, v2 = .ok (.Ok base) → verify = .ok (.Err error) →
      source = .ok (.Err error)) ∧
    (∀ base original, v2 = .ok (.Ok base) → verify = .ok (.Ok original) →
      rebuilt = .ok (.Err error) → source = .ok (.Err error))

theorem native_v3_prefix_exit : ActualNativeV3PrefixExit := by
  intro sumCosts capacity budget beta candidates error source v2 verify rebuilt
  refine ⟨?_, ?_, ?_⟩
  · intro failed
    dsimp only [v2] at failed
    simp only [source, WorkScheduleV3.row_bound, failed, bind_ok, CoreOpsTry.branch,
      CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _
  · intro base passed failed
    dsimp only [v2] at passed
    dsimp only [verify] at failed
    simp only [source, WorkScheduleV3.row_bound, passed, failed, bind_ok,
      CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _
  · intro base original passed checked failed
    dsimp only [v2] at passed
    dsimp only [verify] at checked
    dsimp only [rebuilt] at failed
    simp only [source, WorkScheduleV3.row_bound, passed, checked, failed,
      bind_ok, CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _

#print axioms native_v3_prefix_exit

end BulksketchBridge.RootWorkBudget
