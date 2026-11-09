import BulksketchBridge.RootRunPrice

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts
open ExecutionVerify (checkedNext)

set_option maxHeartbeats 2000000

def affinePreparationCost (degree : Usize) : CostResult :=
  checkedNext (degree.val * degree.val) fun square =>
  checkedNext (square * degree.val) fun cube =>
  checkedNext (5 * cube) fun cubic =>
  checkedNext (16 * square) fun quadratic =>
  checkedNext (cubic + quadratic) fun elimination =>
  checkedNext (327 * degree.val) fun linear =>
  checkedNext (linear + 16900) fun binaryMap =>
  checkedCost (elimination + binaryMap)

theorem affine_preparation_cost_refines (degree : Usize) :
    WorkScheduleV1.cost (.AffinePreparation degree) = .ok (affinePreparationCost degree) := by
  obtain ⟨word, normal, value⟩ := number_refines degree
  have mulEq (left right : U64) :
      mul left right = .ok (checkedCost (left.val * right.val)) := mul_refines left right
  have addEq (left right : U64) :
      add left right = .ok (checkedCost (left.val + right.val)) := BmPrice.add_refines left right
  simp only [WorkScheduleV1.cost, affinePreparationCost, checkedNext, normal, value,
    bind_ok, CoreOpsTry.branch, mulEq, addEq,
    show (5#u64).val = 5 from rfl, show (16#u64).val = 16 from rfl,
    show (327#u64).val = 327 from rfl, show (16900#u64).val = 16900 from rfl]
  repeat' first
  | rfl
  | (split <;> simp_all only [bind_ok, Bind.bind, CoreOpsTry.branch, mulEq, addEq,
      show (5#u64).val = 5 from rfl, show (16#u64).val = 16 from rfl,
      show (327#u64).val = 327 from rfl, show (16900#u64).val = 16900 from rfl,
      CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from])
  | (first | exact bind_ok _ _ | (assumption))


end BulksketchBridge.RootRun
