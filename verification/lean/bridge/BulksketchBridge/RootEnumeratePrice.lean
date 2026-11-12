import BulksketchBridge.RootRunPrice

namespace BulksketchBridge.RootEnumerate

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts
open ExecutionVerify (checkedNext)

set_option maxHeartbeats 2000000

def enumerationCost (degree rank : Usize) : CostResult :=
  if rank.val < 64 then
    checkedNext (2 * 2 ^ rank.val) fun twicePoints =>
    checkedNext (degree.val + 2) fun width =>
    checkedNext (twicePoints * width) fun evaluated =>
    checkedNext (degree.val + 1) fun accepted =>
    checkedCost (evaluated + accepted)
  else .Err .WorkLimitExceeded

private def points (rank : U32) : U64 := ⟨(1#u64).bv <<< rank.val⟩

private theorem points_value (rank : U32) (bounded : rank.val < 64) :
    (points rank).val = 2 ^ rank.val := by
  change ((1#u64).bv <<< rank.val).toNat = _
  rw [BitVec.toNat_shiftLeft, show (1#u64).bv.toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
  change 2 ^ rank.val % 2 ^ 64 = _
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) bounded)]

private theorem reject_rank {rank : Usize} (outside : U32.max < rank.val) :
    core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from rank = Result.ok (.Err ()) := by
  unfold core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from core.num.tryFromUScalar
  simp only [UScalar.max_UScalarTy_U32_eq, Nat.not_le_of_gt outside, ite_false]

private theorem multiply_price (left right : U64) :
    mul left right = .ok (checkedCost (left.val * right.val)) :=
  mul_refines left right

private theorem add_price (left right : U64) :
    add left right = .ok (checkedCost (left.val + right.val)) :=
  BmPrice.add_refines left right

local macro "settle_prices" : tactic => `(tactic|
  repeat' first
  | rfl
  | (split <;> simp_all only [bind_ok, Bind.bind, CoreOpsTry.branch,
      multiply_price, add_price,
      show (1#u64).val = 1 from rfl, show (2#u64).val = 2 from rfl,
      CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from])
  | (first | exact bind_ok _ _ | (assumption)))

theorem enumeration_cost_refines (degree rank : Usize) :
    WorkScheduleV1.cost (.AffineEnumeration degree rank) = .ok (enumerationCost degree rank) := by
  by_cases convertible : rank.val ≤ U32.max
  · obtain ⟨word, converted, rankValue⟩ :=
      checked_unsigned_conversion_normal (target := .U32) rank (by rwa [UScalar.max_UScalarTy_U32_eq])
    have cast : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from rank = Result.ok (.Ok word) :=
      converted
    by_cases small : rank.val < 64
    · have wordSmall : word.val < 64 := by rwa [rankValue]
      obtain ⟨d, degreeNormal, degreeValue⟩ := number_refines degree
      have shifted : core.num.U64.checked_shl 1#u64 word = .ok (some (points word)) := by
        simp only [core.num.U64.checked_shl, wordSmall, ite_true]
        rfl
      have doubled : mul 2#u64 (points word) = .ok (checkedCost (2 * 2 ^ rank.val)) := by
        rw [mul_refines, points_value word wordSmall, rankValue]
        rfl
      simp only [WorkScheduleV1.cost, cast, bind_ok, core.result.Result.map_err_ok, CoreOpsTry.branch,
        shifted, core.option.Option.ok_or, enumerationCost, small, ite_true,
        checkedNext, doubled, degreeNormal]
      have width : add d 2#u64 = .ok (checkedCost (degree.val + 2)) := by rw [BmPrice.add_refines, degreeValue]; rfl
      have fixed : add d 1#u64 = .ok (checkedCost (degree.val + 1)) := by rw [BmPrice.add_refines, degreeValue]; rfl
      cases checkedCost (2 * 2 ^ rank.val) with
      | Err error =>
        simp only [bind_ok,
          CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, Bind.bind]
      | Ok twicePoints =>
        simp only [bind_ok, width]
        cases checkedCost (degree.val + 2) with
        | Err error =>
          simp only [bind_ok,
            CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, Bind.bind]
        | Ok width =>
          simp only [bind_ok, multiply_price]
          cases checkedCost (twicePoints.val * width.val) with
          | Err error =>
            simp only [bind_ok,
              CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, Bind.bind]
          | Ok evaluated =>
            simp only [bind_ok, fixed]
            cases checkedCost (degree.val + 1) <;>
              simp only [bind_ok, add_price]
            all_goals settle_prices
    · have tooLarge : ¬ word.val < 64 := by rwa [rankValue]
      have shifted : core.num.U64.checked_shl 1#u64 word = .ok none := by
        simp only [core.num.U64.checked_shl, tooLarge, ite_false]
      simp only [WorkScheduleV1.cost, cast, bind_ok, core.result.Result.map_err_ok, CoreOpsTry.branch,
        shifted, core.option.Option.ok_or, enumerationCost, small, ite_false,
        CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      simp only [Bind.bind, bind_ok]
  · have outside : U32.max < rank.val := by omega
    have small : ¬ rank.val < 64 := by
      have fits : 64 ≤ U32.max := by rw [U32.max_eq]; decide
      omega
    simp only [WorkScheduleV1.cost, reject_rank outside, bind_ok, enumerationCost, small, ite_false,
      core.result.Result.map_err_err,
      WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError,
      WorkScheduleV1.cost.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorDecodeError.call_once,
      CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, Bind.bind]

end BulksketchBridge.RootEnumerate
