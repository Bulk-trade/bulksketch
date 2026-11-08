import BulksketchBridge.ExecutionVerifyPrice
import BulksketchBridge.ClosedLeafAdvance

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts
open ExecutionVerify (checkedNext)

set_option maxHeartbeats 2000000

def tableCost (degree : Usize) : CostResult :=
  checkedNext (degree.val * degree.val) fun square =>
  checkedNext (8 * square) fun table =>
  checkedNext (2 * degree.val) fun linear =>
  checkedCost (table + linear)

def gcdCost (degree : Usize) : CostResult :=
  checkedNext (degree.val + 1) fun width =>
  checkedNext (width * width) fun square =>
  checkedNext (8 * square) fun quadratic =>
  checkedNext (128 * width) fun linear =>
  checkedCost (quadratic + linear)

def squareModCost (degree : Usize) : CostResult :=
  checkedNext (degree.val * degree.val) fun square =>
  checkedNext (3 * square) fun quadratic =>
  checkedNext (2 * degree.val) fun linear =>
  checkedCost (quadratic + linear)

def affineSplitCost (degree rank : Usize) : CostResult :=
  match squareModCost degree with
  | .Err reason => .Err reason
  | .Ok square =>
    checkedNext (3 * degree.val) fun triple =>
    checkedNext (triple + 3) fun next =>
    checkedNext (square.val + next) fun perRank =>
    checkedNext (rank.val * perRank) fun allRanks =>
    checkedNext (triple + 1) fun fixed =>
    checkedCost (allRanks + fixed)

private theorem multiply_price (left right : U64) :
    mul left right = .ok (checkedCost (left.val * right.val)) :=
  mul_refines left right

private theorem add_price (left right : U64) :
    add left right = .ok (checkedCost (left.val + right.val)) :=
  BmPrice.add_refines left right

private theorem square_cost (degree : Usize) :
    bulksketch.decode.work.square degree = .ok (checkedCost (degree.val * degree.val)) := by
  obtain ⟨word, normal, value⟩ := number_refines degree
  simp only [bulksketch.decode.work.square, normal, bind_ok, CoreOpsTry.branch, multiply_price, value]

local macro "settle_prices" : tactic => `(tactic|
  repeat' first
  | rfl
  | (split <;> simp_all only [bind_ok, Bind.bind, CoreOpsTry.branch, multiply_price, add_price,
      show (1#u64).val = 1 from rfl, show (2#u64).val = 2 from rfl, show (3#u64).val = 3 from rfl,
      show (8#u64).val = 8 from rfl, show (128#u64).val = 128 from rfl,
      CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from])
  | (first | exact bind_ok _ _ | (assumption)))

theorem table_cost_refines (degree : Usize) :
    WorkScheduleV1.cost (.Table degree) = .ok (tableCost degree) := by
  obtain ⟨word, normal, value⟩ := number_refines degree
  simp only [WorkScheduleV1.cost, tableCost, checkedNext, square_cost, normal, value,
    bind_ok, CoreOpsTry.branch, multiply_price, add_price,
    show (8#u64).val = 8 from rfl, show (2#u64).val = 2 from rfl]
  settle_prices

theorem gcd_cost_refines (degree : Usize) :
    WorkScheduleV1.cost (.Gcd degree) = .ok (gcdCost degree) := by
  obtain ⟨word, normal, value⟩ := number_refines degree
  simp only [WorkScheduleV1.cost, gcdCost, checkedNext, normal, value,
    bind_ok, CoreOpsTry.branch, multiply_price, add_price,
    show (1#u64).val = 1 from rfl, show (8#u64).val = 8 from rfl, show (128#u64).val = 128 from rfl]
  settle_prices

theorem square_mod_cost_refines (degree : Usize) :
    square_mod degree = .ok (squareModCost degree) := by
  obtain ⟨word, normal, value⟩ := number_refines degree
  simp only [square_mod, squareModCost, checkedNext, square_cost, normal, value,
    bind_ok, CoreOpsTry.branch, multiply_price, add_price,
    show (2#u64).val = 2 from rfl, show (3#u64).val = 3 from rfl]
  settle_prices

theorem affine_split_cost_refines (degree rank : Usize) :
    WorkScheduleV1.cost (.AffineSplit degree rank) = .ok (affineSplitCost degree rank) := by
  obtain ⟨d, degreeNormal, degreeValue⟩ := number_refines degree
  obtain ⟨r, rankNormal, rankValue⟩ := number_refines rank
  simp only [WorkScheduleV1.cost, affineSplitCost, checkedNext, degreeNormal, degreeValue,
    rankNormal, rankValue, square_mod_cost_refines, bind_ok, CoreOpsTry.branch, multiply_price, add_price,
    show (1#u64).val = 1 from rfl, show (3#u64).val = 3 from rfl]
  settle_prices

theorem roots_charge_returns (meter : WorkMeter) (operation : Charge) (cost : CostResult)
    (priced : WorkScheduleV1.cost operation = .ok cost) :
    bulksketch.decode.roots.charge meter operation = .ok (StageCharge.chargeResult meter cost) := by
  rw [ClosedLeafAdvance.charge_refines, priced, bind_ok]

end BulksketchBridge.RootRun
