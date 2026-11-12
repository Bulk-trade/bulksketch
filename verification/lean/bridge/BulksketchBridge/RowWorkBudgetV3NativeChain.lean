import BulksketchBridge.RowWorkBudgetV3Exact
import BulksketchBridge.RowWorkBudgetV2
import BulksketchBridge.SumCostsNative

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work
open AffineSelector (word)

def v3ExpectedFromFixedPrices (capacity budget beta : Usize) (fixed : Nat) : CostResult :=
  let base := checkedCost (fixed + 2 * capacity.val * BmPrice.bmUnits budget + rootsEnvelope budget.val)
  let verify := .Ok (word (originalVerifyUnits capacity.val beta.val))
  v3U16Expected capacity budget beta (v2Expected capacity budget base verify)

/-- Compose the actual sum, V1, V2 and V3 source calls. Each fixed price
    entry is a checked result of the original six-charge list. -/
def ActualNativeV3FromFixedPrices : Prop :=
  ∀ (capacity budget beta candidates : Usize) (prices : List Nat),
    capacity.val ≤ 65535 → budget.val ≤ 65535 → beta.val ≤ 65535 →
    List.Forall₂ (fun charge units => WorkScheduleV1.cost charge = .ok (checkedCost units))
      (v1FixedCharges capacity budget beta candidates).val prices →
    WorkScheduleV3.row_bound bulksketch.decode.work.sum_costs capacity budget beta candidates =
      .ok (v3ExpectedFromFixedPrices capacity budget beta prices.sum)

theorem native_v3_from_fixed_prices : ActualNativeV3FromFixedPrices := by
  intro capacity budget beta candidates prices capacityMax budgetMax betaMax actualPrices
  have v1 := native_v1_row_bound_from_prices bulksketch.decode.work.sum_costs
    capacity budget beta candidates prices native_sum_costs actualPrices capacityMax budgetMax
  have verify := (native_v3_verifier_quotes capacity budget beta capacityMax budgetMax betaMax).1
  have v2 := native_v2_row_bound bulksketch.decode.work.sum_costs capacity budget beta candidates _ _ v1 verify
  exact native_v3_u16_row_bound bulksketch.decode.work.sum_costs capacity budget beta candidates _
    capacityMax budgetMax betaMax v2

#print axioms native_v3_from_fixed_prices

end BulksketchBridge.RootWorkBudget
