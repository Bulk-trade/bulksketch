import BulksketchBridge.ExecutionVerifyPriceSpec
import BulksketchBridge.ExecutionVerify
import BulksketchBridge.BmPrice

namespace BulksketchBridge.ExecutionVerify

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts

set_option maxHeartbeats 2000000

private theorem multiply (left right : U64) :
    mul left right = .ok (checkedCost (left.val * right.val)) :=
  mul_refines left right

private theorem addition (left right : U64) :
    add left right = .ok (checkedCost (left.val + right.val)) :=
  BmPrice.add_refines left right

private theorem direct_cost_refines (capacity outputBudget : Usize) :
    WorkScheduleV1.cost (.Verify capacity outputBudget) = .ok (directCost capacity outputBudget) := by
  obtain ⟨c, capacityNormal, capacityValue⟩ := number_refines capacity
  obtain ⟨b, budgetNormal, budgetValue⟩ := number_refines outputBudget
  have oneValue : (1#u64).val = 1 := rfl
  have twoValue : (2#u64).val = 2 := rfl
  have threeValue : (3#u64).val = 3 := rfl
  simp only [WorkScheduleV1.cost, directCost, checkedNext, capacityNormal, budgetNormal, bind_ok,
    CoreOpsTry.branch, multiply, addition, capacityValue, budgetValue, oneValue, twoValue, threeValue]
  cases checkedCost (2 * outputBudget.val) with
  | Err error =>
    simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _
  | Ok twice =>
    simp only [bind_ok]
    cases checkedCost (twice.val + 3) with
    | Err error =>
      simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      exact bind_ok _ _
    | Ok perWord =>
      simp only [bind_ok]
      cases checkedCost (perWord.val * capacity.val) with
      | Err error =>
        simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
        exact bind_ok _ _
      | Ok words =>
        simp only [bind_ok]
        cases checkedCost (outputBudget.val + 1) with
        | Err error =>
          simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
          exact bind_ok _ _
        | Ok outputs =>
          simp only [bind_ok]
          cases checkedCost (words.val + outputs.val) <;>
            simp [CoreOpsTry_traitFromResidualResult.from_residual]

private theorem rebuilt_cost_refines (capacity outputBudget degree : Usize) :
    WorkScheduleV1.cost (.VerifyLfsr capacity outputBudget degree) = .ok (rebuiltCost capacity outputBudget degree) := by
  obtain ⟨c, capacityNormal, capacityValue⟩ := number_refines capacity
  obtain ⟨b, budgetNormal, budgetValue⟩ := number_refines outputBudget
  obtain ⟨d, degreeNormal, degreeValue⟩ := number_refines degree
  have threeValue : (3#u64).val = 3 := rfl
  have fourValue : (4#u64).val = 4 := rfl
  simp only [WorkScheduleV1.cost, rebuiltCost, checkedNext, capacityNormal, budgetNormal, degreeNormal, bind_ok,
    CoreOpsTry.branch, multiply, addition, capacityValue, budgetValue, degreeValue, threeValue, fourValue]
  cases checkedCost (3 * degree.val) with
  | Err error =>
    simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _
  | Ok triple =>
    simp only [bind_ok]
    cases checkedCost (triple.val + 4) with
    | Err error =>
      simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      exact bind_ok _ _
    | Ok perWord =>
      simp only [bind_ok]
      cases checkedCost (perWord.val * capacity.val) with
      | Err error =>
        simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
        exact bind_ok _ _
      | Ok words =>
        simp only [bind_ok]
        cases checkedCost (outputBudget.val + 3) with
        | Err error =>
          simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
          exact bind_ok _ _
        | Ok outputs =>
          simp only [bind_ok]
          cases checkedCost (degree.val + outputs.val) with
          | Err error =>
            simp only [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
            exact bind_ok _ _
          | Ok candidates =>
            simp only [bind_ok]
            cases checkedCost (words.val + candidates.val) <;>
              simp [CoreOpsTry_traitFromResidualResult.from_residual]

theorem actual_cost_refines {F K : Type} (self : Execution F K) (input : RowInput) :
    WorkScheduleV1.cost (priceTag self input) = .ok (actualCost self input) := by
  unfold priceTag actualCost
  split <;> simp_all only [direct_cost_refines, rebuilt_cost_refines]

theorem verify_with_prices_refines : ActualExecutionVerifyWithPrices := by
  intro K kernels self input workspace meter seed continued bounds
  exact verify_refines kernels self input workspace meter (actualCost self input) seed continued
    (actual_cost_refines self input) bounds

end BulksketchBridge.ExecutionVerify
