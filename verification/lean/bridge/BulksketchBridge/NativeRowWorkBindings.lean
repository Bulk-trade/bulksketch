import BulksketchBridge.SumCostsNative
import BulksketchBridge.RowWorkBudgetV2

namespace BulksketchBridge.RootWorkBudget

open Aeneas.Std WorkSchedule
open bulksketch.decode.work

/-- The original V1 wrapper uses the original sum caller and its proved
ordered fold, with each fixed price and the u16 dimension bounds explicit. -/
def ActualNativeV1RowBoundWithSum : Prop :=
  ∀ (capacity budget beta candidates : Usize) (prices : List Nat),
    List.Forall₂ (fun charge units => WorkScheduleV1.cost charge = .ok (checkedCost units))
      (v1FixedCharges capacity budget beta candidates).val prices →
    capacity.val ≤ 65535 → budget.val ≤ 65535 →
    WorkScheduleV1.row_bound sum_costs capacity budget beta candidates =
      .ok (checkedCost (prices.sum + 2 * capacity.val * BmPrice.bmUnits budget + rootsEnvelope budget.val))

theorem native_v1_row_bound_with_sum : ActualNativeV1RowBoundWithSum := by
  intro capacity budget beta candidates prices fixed capacityBound budgetBound
  exact native_v1_row_bound_from_prices sum_costs capacity budget beta candidates prices
    native_sum_costs fixed capacityBound budgetBound

/-- Bind both wrapper calls to the original sum and preserve the separate
price of a tiny probe verification. -/
def ActualNativeV2RowBoundWithSum : Prop :=
  ∀ (capacity budget beta candidates : Usize) (prices : List Nat) (verify : CostResult),
    List.Forall₂ (fun charge units => WorkScheduleV1.cost charge = .ok (checkedCost units))
      (v1FixedCharges capacity budget beta candidates).val prices →
    capacity.val ≤ 65535 → budget.val ≤ 65535 →
    WorkScheduleV1.cost (.Verify capacity beta) = .ok verify →
    WorkScheduleV2.row_bound sum_costs capacity budget beta candidates =
      .ok (v2Expected capacity budget
        (checkedCost (prices.sum + 2 * capacity.val * BmPrice.bmUnits budget + rootsEnvelope budget.val)) verify)

theorem native_v2_row_bound_with_sum : ActualNativeV2RowBoundWithSum := by
  intro capacity budget beta candidates prices verify fixed capacityBound budgetBound verifyPrice
  exact native_v2_row_bound sum_costs capacity budget beta candidates _ verify
    (native_v1_row_bound_with_sum capacity budget beta candidates prices fixed capacityBound budgetBound) verifyPrice

#print axioms native_v1_row_bound_with_sum
#print axioms native_v2_row_bound_with_sum

end BulksketchBridge.RootWorkBudget
