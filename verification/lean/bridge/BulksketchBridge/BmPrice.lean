import BulksketchBridge.BmPriceSpec
import BulksketchBridge.WorkSchedule

namespace BulksketchBridge.BmPrice

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work

theorem add_refines : CheckedAddRefines := by
  intro left right
  have correct := U64.checked_add_bv_spec left right
  unfold add
  simp only [lift, bind_ok]
  apply checked_operation
  cases checked : U64.checked_add left right <;> simp only [checked] at correct ⊢
  · exact correct
  · exact ⟨correct.1, correct.2.1⟩

private theorem checked_error (units : Nat) (error : bulksketch.types.DecodeError)
    (failed : checkedCost units = .Err error) : U64.max < units ∧ error = .WorkLimitExceeded := by
  by_cases fits : units ≤ U64.max
  · simp [checkedCost, fits] at failed
  · simp [checkedCost, fits] at failed
    exact ⟨by omega, failed.symm⟩

theorem bm_price_refines : ActualBmPriceRefines := by
  intro budget
  obtain ⟨word, converted, wordVal⟩ := number_refines budget
  have first : add word 1#u64 = .ok (checkedCost (budget.val + 1)) := by
    rw [add_refines, wordVal]
    rfl
  cases stage1 : checkedCost (budget.val + 1) with
  | Err error =>
    obtain ⟨overflow, rfl⟩ := checked_error _ _ stage1
    have large : ¬ bmUnits budget ≤ U64.max := by unfold bmUnits; omega
    have final : checkedCost (bmUnits budget) = .Err .WorkLimitExceeded := by
      rw [checkedCost, dite_eq_right large]
    simp only [WorkScheduleV1.cost, converted, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      first, stage1, final,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    exact bind_ok _ _
  | Ok width =>
    have exactWidth := ((checked_cost_ok_iff _ _).mp stage1).2
    have second : mul 6#u64 width = .ok (checkedCost (6 * (budget.val + 1))) := by
      rw [mul_refines, exactWidth]
      rfl
    cases stage2 : checkedCost (6 * (budget.val + 1)) with
    | Err error =>
      obtain ⟨overflow, rfl⟩ := checked_error _ _ stage2
      have large : ¬ bmUnits budget ≤ U64.max := by unfold bmUnits; omega
      have final : checkedCost (bmUnits budget) = .Err .WorkLimitExceeded := by
        rw [checkedCost, dite_eq_right large]
      simp only [WorkScheduleV1.cost, converted, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
        first, stage1, second, stage2, final,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      exact bind_ok _ _
    | Ok subtotal =>
      have exactSubtotal := ((checked_cost_ok_iff _ _).mp stage2).2
      have third : add subtotal 128#u64 = .ok (checkedCost (bmUnits budget)) := by
        rw [add_refines, exactSubtotal]
        rfl
      cases final : checkedCost (bmUnits budget) <;>
        simp [WorkScheduleV1.cost, converted, core.result.Result.Insts.CoreOpsTry.branch,
          first, stage1, second, stage2, third, final,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

end BulksketchBridge.BmPrice
