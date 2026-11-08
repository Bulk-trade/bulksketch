import BulksketchBridge.WorkSchedule
import BulksketchBridge.ClosedLeafSpec

namespace BulksketchBridge.ClosedLeaf

open Aeneas Aeneas.Std bulksketch.decode.work

theorem leaf_three : WorkScheduleV1.cost .LeafThree = Result.ok (.Ok 640#u64) := rfl

theorem leaf_four : WorkScheduleV1.cost .LeafFour = Result.ok (.Ok 2048#u64) := rfl

private theorem number_of_value (degree : Usize) (word : U64) (value : degree.val = word.val) :
    number degree = Result.ok (.Ok word) := by
  obtain ⟨converted, normal, exactValue⟩ := BulksketchBridge.WorkSchedule.number_refines degree
  have same : converted = word := UScalar.eq_of_val_eq (exactValue.trans value)
  rw [normal, same]

private theorem mul_of_value (left right word : U64) (value : word.val = left.val * right.val) :
    mul left right = Result.ok (.Ok word) := by
  have fits : word.val ≤ U64.max := by scalar_tac
  rw [BulksketchBridge.WorkSchedule.mul_refines,
    (BulksketchBridge.WorkSchedule.checked_cost_ok_iff _ _).mpr ⟨value ▸ fits, value⟩]

private theorem add_of_value (left right word : U64) (value : word.val = left.val + right.val) :
    add left right = Result.ok (.Ok word) := by
  have fits : word.val ≤ U64.max := by scalar_tac
  have exactSum := U64.checked_add_bv_spec left right
  cases result : U64.checked_add left right with
  | none =>
    simp only [result] at exactSum
    omega
  | some sum =>
    simp only [result] at exactSum
    have same : sum = word := UScalar.eq_of_val_eq (exactSum.2.1.trans value.symm)
    simp only [add, result, lift, bind_ok, core.option.Option.ok_or, same]

theorem factor_verification_three :
    WorkScheduleV1.cost (.FactorVerification 3#usize) = Result.ok (.Ok 31#u64) := by
  have normal := number_of_value 3#usize 3#u64 (by simp)
  simp only [WorkScheduleV1.cost, square, normal,
    mul_of_value 3#u64 3#u64 9#u64 rfl, mul_of_value 2#u64 9#u64 18#u64 rfl,
    mul_of_value 4#u64 3#u64 12#u64 rfl, add_of_value 18#u64 12#u64 30#u64 rfl,
    add_of_value 30#u64 1#u64 31#u64 rfl, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]

theorem factor_verification_four :
    WorkScheduleV1.cost (.FactorVerification 4#usize) = Result.ok (.Ok 49#u64) := by
  have normal := number_of_value 4#usize 4#u64 (by simp)
  simp only [WorkScheduleV1.cost, square, normal,
    mul_of_value 4#u64 4#u64 16#u64 rfl, mul_of_value 2#u64 16#u64 32#u64 rfl,
    add_of_value 32#u64 16#u64 48#u64 rfl, add_of_value 48#u64 1#u64 49#u64 rfl,
    bind_ok, core.result.Result.Insts.CoreOpsTry.branch]

theorem price_refines (roots : bulksketch.decode.roots.Roots) (stage : bulksketch.types.Stage)
    (degree : roots.degree = 3#usize ∨ roots.degree = 4#usize) :
    WorkScheduleV1.cost (leafOperation roots stage) = Result.ok (.Ok (leafPrice roots stage)) := by
  rcases degree with three | four <;> cases isVerification : verifying stage <;>
    simp [leafOperation, leafPrice, *, leaf_three, leaf_four,
      factor_verification_three, factor_verification_four]

end BulksketchBridge.ClosedLeaf
