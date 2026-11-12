import Arithmetic.RowWorkBudgetGenerated
import BulksketchBridge.RootWorkBudgetNative
import BulksketchBridge.BmPrice

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def v1FixedCharges (capacity budget beta candidates : Usize) : Slice Charge :=
  (Array.make 6#usize [.Compare capacity, .Reconstruct capacity, .Candidates budget candidates,
    .Deflate budget, .Verify capacity beta, .Canonicalize beta]).to_slice

/-- A concrete checked fold contract for the opaque original sum slot.
    It propagates the first original pricing or addition error. -/
noncomputable def foldCosts : List Charge → U64 → Result CostResult
  | [], total => .ok (.Ok total)
  | charge :: tail, total => do
    let price ← WorkScheduleV1.cost charge
    match price with
    | .Err error => .ok (.Err error)
    | .Ok amount =>
      let result ← add total amount
      match result with
      | .Err error => .ok (.Err error)
      | .Ok next => foldCosts tail next

def SumCostsRefines (sumCosts : RowWorkBudgetRuntime.SumCosts) : Prop :=
  ∀ charges, sumCosts charges = foldCosts charges.val 0#u64

private theorem checked_exists (units : Nat) (fits : units ≤ U64.max) :
    ∃ word : U64, checkedCost units = .Ok word ∧ word.val = units := by
  unfold checkedCost
  rw [dite_eq_left fits]
  exact ⟨_, rfl, UScalar.ofNatCore_val_eq _⟩

/-- The admitted sum contract is an ordered checked left fold. Every
    intermediate addition is nondecreasing, so the fold's single final
    natural check also accounts for early pricing or addition overflow. -/
theorem fold_costs_from_prices {charges : List Charge} {prices : List Nat}
    (bound : List.Forall₂
      (fun charge units => WorkScheduleV1.cost charge = .ok (checkedCost units)) charges prices)
    (total : U64) :
    foldCosts charges total = .ok (checkedCost (total.val + prices.sum)) := by
  induction bound generalizing total with
  | nil =>
    have normal := (checked_cost_ok_iff total.val total).mpr ⟨by simpa only [U64.max_eq] using total.le_max, rfl⟩
    simp only [foldCosts, List.sum_nil, Nat.add_zero, normal]
  | @cons charge units charges prices head tail ih =>
    by_cases unitsFit : units ≤ U64.max
    · obtain ⟨amount, amountOk, amountValue⟩ := checked_exists units unitsFit
      have headCall : WorkScheduleV1.cost charge = .ok (.Ok amount) :=
        head.trans (congrArg Result.ok amountOk)
      have addCall : add total amount = .ok (checkedCost (total.val + units)) := by
        rw [BmPrice.add_refines, amountValue]
      by_cases totalFit : total.val + units ≤ U64.max
      · obtain ⟨next, nextOk, nextValue⟩ := checked_exists _ totalFit
        simp only [foldCosts, headCall, addCall, bind_ok, nextOk, ih, nextValue, List.sum_cons, Nat.add_assoc]
      · have nextErr : checkedCost (total.val + units) = .Err .WorkLimitExceeded := by
          rw [checkedCost, dite_eq_right totalFit]
        have fullErr : checkedCost (total.val + (units :: prices).sum) = .Err .WorkLimitExceeded := by
          rw [List.sum_cons, checkedCost, dite_eq_right (by omega)]
        simp only [foldCosts, headCall, bind_ok, addCall, nextErr, fullErr]
    · have amountErr : checkedCost units = .Err .WorkLimitExceeded := by
        rw [checkedCost, dite_eq_right unitsFit]
      have fullErr : checkedCost (total.val + (units :: prices).sum) = .Err .WorkLimitExceeded := by
        rw [List.sum_cons, checkedCost, dite_eq_right (by omega)]
      simp only [foldCosts, head, amountErr, bind_ok, fullErr]

/-- Exact source V1 row wrapper. The checked sum contract attaches the
    fixed ordered charge list to the independent fold. Both original
    post-fold additions preserve the WorkLimitExceeded exit. -/
def ActualNativeV1RowBound : Prop :=
  ∀ (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity budget beta candidates : Usize) (fixed : Nat),
    SumCostsRefines sumCosts →
    foldCosts (v1FixedCharges capacity budget beta candidates).val 0#u64 = .ok (checkedCost fixed) →
    capacity.val ≤ 65535 → budget.val ≤ 65535 →
    WorkScheduleV1.row_bound sumCosts capacity budget beta candidates =
      .ok (checkedCost (fixed + 2 * capacity.val * BmPrice.bmUnits budget + rootsEnvelope budget.val))

theorem native_v1_row_bound : ActualNativeV1RowBound := by
  intro sumCosts capacity budget beta candidates fixed sumRefines fold capacityMax budgetMax
  have fixedCall := (sumRefines (v1FixedCharges capacity budget beta candidates)).trans fold
  have sourceFixed : sumCosts (Array.make 6#usize
      [.Compare capacity, .Reconstruct capacity, .Candidates budget candidates, .Deflate budget,
        .Verify capacity beta, .Canonicalize beta]).to_slice = .ok (checkedCost fixed) := fixedCall
  by_cases fixedFits : fixed ≤ U64.max
  · obtain ⟨fixedWord, fixedOk, fixedValue⟩ := checked_exists fixed fixedFits
    obtain ⟨capacityWord, capacityCall, capacityValue⟩ := number_refines capacity
    have twoFits : 2 * capacity.val ≤ U64.max := by rw [U64.max_eq]; omega
    obtain ⟨two, twoOk, twoValue⟩ := checked_exists _ twoFits
    have twoCall : mul 2#u64 capacityWord = .ok (.Ok two) := by
      rw [mul_refines, capacityValue]
      exact congrArg Result.ok twoOk
    have bmBound : BmPrice.bmUnits budget ≤ 393344 := by unfold BmPrice.bmUnits; omega
    have bmFits : BmPrice.bmUnits budget ≤ U64.max := by rw [U64.max_eq]; omega
    obtain ⟨bmWord, bmOk, bmValue⟩ := checked_exists _ bmFits
    have bmCall : WorkScheduleV1.cost (.BmStep budget) = .ok (.Ok bmWord) := by
      rw [BmPrice.bm_price_refines, bmOk]
    have workBound : 2 * capacity.val * BmPrice.bmUnits budget ≤ 131070 * 393344 :=
      Nat.mul_le_mul (by omega) bmBound
    have workFits : 2 * capacity.val * BmPrice.bmUnits budget ≤ U64.max := by rw [U64.max_eq]; omega
    obtain ⟨work, workOk, workValue⟩ := checked_exists _ workFits
    have workCall : mul two bmWord = .ok (.Ok work) := by
      rw [mul_refines, twoValue, bmValue, workOk]
    have subtotalCall : add fixedWord work = .ok (checkedCost (fixed + work.val)) := by
      rw [BmPrice.add_refines, fixedValue]
    by_cases subtotalFits : fixed + work.val ≤ U64.max
    · obtain ⟨subtotal, subtotalOk, subtotalValue⟩ := checked_exists _ subtotalFits
      obtain ⟨roots, rootsCall, rootsValue⟩ := native_roots_bound budget budgetMax
      have totalCall : add subtotal roots = .ok (checkedCost (fixed + work.val + rootsEnvelope budget.val)) := by
        rw [BmPrice.add_refines, subtotalValue, rootsValue]
      have subtotalNormal : add fixedWord work = .ok (.Ok subtotal) := subtotalCall.trans (congrArg Result.ok subtotalOk)
      rw [workValue] at totalCall
      simp only [WorkScheduleV1.row_bound, lift, sourceFixed, fixedOk, bind_ok, CoreOpsTry.branch, capacityCall,
        twoCall, bmCall, workCall, subtotalNormal, rootsCall, totalCall]
      cases checkedCost
          (fixed + 2 * capacity.val * BmPrice.bmUnits budget + rootsEnvelope budget.val) <;>
        simp [bind_ok, CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    · have subtotalErr : checkedCost (fixed + work.val) = .Err .WorkLimitExceeded := by
        rw [checkedCost, dite_eq_right subtotalFits]
      have totalErr : checkedCost (fixed + 2 * capacity.val * BmPrice.bmUnits budget + rootsEnvelope budget.val) =
          .Err .WorkLimitExceeded := by
        rw [← workValue, checkedCost, dite_eq_right (by omega)]
      simp [WorkScheduleV1.row_bound, lift, sourceFixed, fixedOk, bind_ok, CoreOpsTry.branch, capacityCall,
        twoCall, bmCall, workCall, subtotalCall, subtotalErr, totalErr,
        CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  · have fixedErr : checkedCost fixed = .Err .WorkLimitExceeded := by
      rw [checkedCost, dite_eq_right fixedFits]
    have totalErr : checkedCost (fixed + 2 * capacity.val * BmPrice.bmUnits budget + rootsEnvelope budget.val) =
        .Err .WorkLimitExceeded := by
      rw [checkedCost, dite_eq_right (by omega)]
    simp [WorkScheduleV1.row_bound, lift, sourceFixed, fixedErr, bind_ok, CoreOpsTry.branch, totalErr,
      CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

def ActualNativeV1RowBoundFromPrices : Prop :=
  ∀ (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity budget beta candidates : Usize) (prices : List Nat),
    SumCostsRefines sumCosts →
    List.Forall₂ (fun charge units => WorkScheduleV1.cost charge = .ok (checkedCost units))
      (v1FixedCharges capacity budget beta candidates).val prices →
    capacity.val ≤ 65535 → budget.val ≤ 65535 →
    WorkScheduleV1.row_bound sumCosts capacity budget beta candidates =
      .ok (checkedCost (prices.sum + 2 * capacity.val * BmPrice.bmUnits budget + rootsEnvelope budget.val))

theorem native_v1_row_bound_from_prices : ActualNativeV1RowBoundFromPrices := by
  intro sumCosts capacity budget beta candidates prices sumRefines actualPrices capacityMax budgetMax
  apply native_v1_row_bound sumCosts capacity budget beta candidates prices.sum sumRefines
  · simpa only [show (0#u64).val = 0 from rfl, Nat.zero_add] using fold_costs_from_prices actualPrices 0#u64
  · exact capacityMax
  · exact budgetMax

#print axioms native_v1_row_bound_from_prices
#print axioms native_v1_row_bound

end BulksketchBridge.RootWorkBudget
