import BulksketchBridge.RowWorkBudgetV3NativeChain
import BulksketchBridge.CandidateEntry
import BulksketchBridge.CanonicalizePrice
import BulksketchBridge.DeflatePrice

namespace BulksketchBridge.RootWorkBudget

open Aeneas Aeneas.Std WorkSchedule
open bulksketch.decode.work
open core.result.Result.Insts
open AffineSelector (word word_val)

def v1FixedPriceUnits (capacity budget beta candidates : Usize) : List Nat :=
  [capacity.val + 1, 3 * capacity.val, 2 * candidates.val * (budget.val + 1),
    Deflation.deflateUnits budget, originalVerifyUnits capacity.val beta.val,
    CanonicalizePrice.units beta]

private theorem checkedWord (units : Nat) (fits : units ≤ U64.max) :
    checkedCost units = .Ok (word units) :=
  (checked_cost_ok_iff ..).mpr ⟨fits, word_val _ fits⟩

private theorem candidate_price_exact (budget candidates : Usize) (budgetMax : budget.val ≤ 65535) :
    WorkScheduleV1.cost (.Candidates budget candidates) =
      .ok (checkedCost (2 * candidates.val * (budget.val + 1))) := by
  rw [CandidateOuter.candidate_cost_refines, CandidateOuter.candidateCost]
  have widthFits : budget.val + 1 ≤ U64.max := by rw [U64.max_eq]; omega
  by_cases doubledFits : 2 * candidates.val ≤ U64.max
  · simp only [checkedWord _ doubledFits, checkedWord _ widthFits,
      word_val _ doubledFits, word_val _ widthFits]
  · have termLe : 2 * candidates.val ≤ 2 * candidates.val * (budget.val + 1) := by
      conv_lhs => rw [← Nat.mul_one (2 * candidates.val)]
      exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))
    have totalFails : ¬ 2 * candidates.val * (budget.val + 1) ≤ U64.max := by omega
    simp only [checkedCost, dite_eq_right doubledFits, dite_eq_right totalFails]

private theorem compare_price_exact (capacity : Usize) (capacityMax : capacity.val ≤ 65535) :
    WorkScheduleV1.cost (.Compare capacity) = .ok (checkedCost (capacity.val + 1)) := by
  obtain ⟨value, counted, exactValue⟩ := number_refines capacity
  have charged : add value 1#u64 = .ok (checkedCost (capacity.val + 1)) := by
    rw [BmPrice.add_refines, exactValue]
    rfl
  have affordable : capacity.val + 1 ≤ U64.max := by rw [U64.max_eq]; omega
  simp only [WorkScheduleV1.cost, counted, bind_ok, CoreOpsTry.branch, charged, checkedWord _ affordable]

theorem native_v1_fixed_price_list (capacity budget beta candidates : Usize)
    (capacityMax : capacity.val ≤ 65535) (budgetMax : budget.val ≤ 65535) (betaMax : beta.val ≤ 65535) :
    List.Forall₂ (fun charge units => WorkScheduleV1.cost charge = .ok (checkedCost units))
      (v1FixedCharges capacity budget beta candidates).val (v1FixedPriceUnits capacity budget beta candidates) := by
  obtain ⟨verify, _, verifyBound, _⟩ := native_v3_verifier_quotes capacity budget beta capacityMax budgetMax betaMax
  have verifyExact : WorkScheduleV1.cost (.Verify capacity beta) =
      .ok (checkedCost (originalVerifyUnits capacity.val beta.val)) := by
    rw [verify, checkedWord _ (by omega)]
  change List.Forall₂ (fun charge units => WorkScheduleV1.cost charge = .ok (checkedCost units))
    [.Compare capacity, .Reconstruct capacity, .Candidates budget candidates, .Deflate budget,
      .Verify capacity beta, .Canonicalize beta] _
  unfold v1FixedPriceUnits
  exact .cons (compare_price_exact capacity capacityMax)
    (.cons (reconstruct_refines capacity)
      (.cons (candidate_price_exact budget candidates budgetMax)
        (.cons (Deflation.deflate_price budget)
          (.cons verifyExact (.cons (CanonicalizePrice.price_refines beta) .nil)))))

/-- The native V3 row bound composes all actual price functions and the
    original sum and V1/V2 wrappers for every admitted u16 dimension.
    Candidate count is unrestricted and every checked overflow is kept. -/
def ActualNativeCompleteV3RowBound : Prop :=
  ∀ (capacity budget beta candidates : Usize),
    capacity.val ≤ 65535 → budget.val ≤ 65535 → beta.val ≤ 65535 →
    WorkScheduleV3.row_bound bulksketch.decode.work.sum_costs capacity budget beta candidates =
      .ok (v3ExpectedFromFixedPrices capacity budget beta (v1FixedPriceUnits capacity budget beta candidates).sum)

theorem native_complete_v3_row_bound : ActualNativeCompleteV3RowBound := by
  intro capacity budget beta candidates capacityMax budgetMax betaMax
  exact native_v3_from_fixed_prices capacity budget beta candidates _
    capacityMax budgetMax betaMax
    (native_v1_fixed_price_list capacity budget beta candidates capacityMax budgetMax betaMax)

#print axioms native_complete_v3_row_bound

end BulksketchBridge.RootWorkBudget
