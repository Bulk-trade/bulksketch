import BulksketchBridge.BmPrice

namespace BulksketchBridge.Deflation

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types

def deflateUnits (degree : Usize) : Nat := 2 * degree.val * (degree.val + 1)

def deflateCost (degree : Usize) : CostResult := checkedCost (deflateUnits degree)

private theorem checked_error (units : Nat) (error : DecodeError)
    (failed : checkedCost units = .Err error) : U64.max < units ∧ error = .WorkLimitExceeded := by
  by_cases fits : units ≤ U64.max
  · simp [checkedCost, fits] at failed
  · simp [checkedCost, fits] at failed
    exact ⟨by omega, failed.symm⟩

private theorem cost_overflow (degree : Usize) (large : U64.max < deflateUnits degree) :
    deflateCost degree = .Err .WorkLimitExceeded := by
  simp only [deflateCost, checkedCost, dite_eq_right (Nat.not_le_of_gt large)]

def ActualNativeDeflatePrice : Prop :=
  ∀ degree, WorkScheduleV1.cost (.Deflate degree) = .ok (deflateCost degree)

theorem deflate_price : ActualNativeDeflatePrice := by
  intro degree
  obtain ⟨word, converted, wordValue⟩ := number_refines degree
  have first : mul 2#u64 word = .ok (checkedCost (2 * degree.val)) := by
    rw [mul_refines, wordValue]
    rfl
  cases doubled : checkedCost (2 * degree.val) with
  | Err error =>
    obtain ⟨overflow, rfl⟩ := checked_error _ _ doubled
    have price := cost_overflow degree
      (overflow.trans_le (Nat.le_mul_of_pos_right _ (by omega)))
    simp [WorkScheduleV1.cost, converted, first, doubled, price,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  | Ok twice =>
    have twiceValue := ((checked_cost_ok_iff _ _).mp doubled).2
    have second : add word 1#u64 = .ok (checkedCost (degree.val + 1)) := by
      rw [BmPrice.add_refines, wordValue]
      rfl
    cases increased : checkedCost (degree.val + 1) with
    | Err error =>
      obtain ⟨overflow, rfl⟩ := checked_error _ _ increased
      have maxOne : 1 ≤ U64.max := by rw [U64.max_eq]; decide
      have price := cost_overflow degree
        (overflow.trans_le (Nat.le_mul_of_pos_left _ (by omega)))
      simp [WorkScheduleV1.cost, converted, first, doubled, second, increased, price,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    | Ok next =>
      have nextValue := ((checked_cost_ok_iff _ _).mp increased).2
      have third : mul twice next = .ok (deflateCost degree) := by
        rw [mul_refines, twiceValue, nextValue]
        rfl
      cases final : deflateCost degree <;>
        simp [WorkScheduleV1.cost, converted, first, doubled, second, increased, third, final,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

#print axioms deflate_price

end BulksketchBridge.Deflation
