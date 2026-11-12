import BulksketchBridge.WorkScheduleSpec
import Arithmetic.MapsRuntime

namespace BulksketchBridge.WorkSchedule

open Aeneas Aeneas.Std

/-- Conversion from either supported pointer width to u64 is exact. -/
theorem number_refines : NumberRefines := by
  intro value
  have sourceBound := value.hBounds
  change value.val < 2 ^ System.Platform.numBits at sourceBound
  have widthBound : 2 ^ System.Platform.numBits ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) System.Platform.numBits_le
  have bounded : value.val ≤ UScalar.max .U64 := by
    rw [UScalar.max_UScalarTy_U64_eq, U64.max_eq]
    omega
  obtain ⟨word, converted, exactValue⟩ := checked_unsigned_conversion_normal value bounded
  refine ⟨word, ?_, exactValue⟩
  simp only [bulksketch.decode.work.number, U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from,
    converted, bind_ok, core.result.Result.map_err_ok]

theorem checked_cost_ok_iff (units : Nat) (word : U64) :
    checkedCost units = .Ok word ↔ units ≤ U64.max ∧ word.val = units := by
  by_cases bounded : units ≤ U64.max
  · rw [checkedCost, dite_eq_left bounded]
    constructor
    · intro equal
      exact ⟨bounded, (congrArg UScalar.val (core.result.Result.Ok.inj equal)).symm⟩
    · rintro ⟨_, value⟩
      congr 1
      exact UScalar.eq_of_val_eq value.symm
  · simp [checkedCost, bounded]

theorem checked_operation (result : Option U64) (units : Nat)
    (correct : match result with
      | some word => units ≤ U64.max ∧ word.val = units
      | none => U64.max < units) :
    core.option.Option.ok_or result bulksketch.types.DecodeError.WorkLimitExceeded =
      Result.ok (checkedCost units) := by
  cases result with
  | none =>
    rw [checkedCost, dite_eq_right (Nat.not_le_of_gt correct)]
    rfl
  | some word =>
    rw [(checked_cost_ok_iff units word).mpr correct]
    rfl

/-- The source checked multiply returns the exact natural product or the
original work-limit error. -/
theorem mul_refines : CheckedMultiplyRefines := by
  intro left right
  have correct := U64.checked_mul_bv_spec left right
  unfold bulksketch.decode.work.mul
  simp only [lift, bind_ok]
  apply checked_operation
  cases checked : U64.checked_mul left right <;> simp only [checked] at correct ⊢
  · exact correct
  · exact ⟨correct.1, correct.2.1⟩

theorem reconstruct_refines : ReconstructCostRefines := by
  intro capacity
  obtain ⟨word, numberNormal, wordValue⟩ := number_refines capacity
  have multiplication : bulksketch.decode.work.mul 3#u64 word =
      Result.ok (reconstructCost capacity) := by
    rw [mul_refines, wordValue]
    rfl
  simp only [bulksketch.decode.work.WorkScheduleV1.cost, numberNormal, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, multiplication]
  cases reconstructCost capacity <;>
    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end BulksketchBridge.WorkSchedule
