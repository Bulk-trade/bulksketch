import BulksketchBridge.BmEntrySpec
import BulksketchBridge.BmPrice
import BulksketchBridge.StageCharge
import BulksketchBridge.RebuiltLfsr
import BulksketchBridge.ReconstructionLoop

namespace BulksketchBridge.BmEntry

open Aeneas Aeneas.Std Aeneas.Std.WP DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

@[simp] theorem tail_length (words : Slice U64) (split : Nat) :
    (tail words split).length = words.length - split := by
  simp [tail, Slice.length]

theorem splitBack_length (words : Slice U64) (split : Nat) (parts : Slice U64 × Slice U64) :
    (splitBack words split parts).length = words.length := by
  unfold splitBack
  split
  · rename_i equal
    simp only [Slice.length, Slice.from_val, List.length_append]
    change parts.1.length + parts.2.length = words.length
    omega
  · rfl

/-- Exact pinned split and its complete two-piece backward function. -/
theorem split_refines (words : Slice U64) (split : Usize) (fits : split.val ≤ words.length) :
    core.slice.Slice.split_at_mut words split =
      .ok ((prefixSlice words split.val, tail words split.val), splitBack words split.val) := by
  have bounded : split ≤ words.length := fits
  unfold core.slice.Slice.split_at_mut
  rw [dite_eq_left bounded]
  dsimp! only
  simp only [List.splitAt_eq, splitBack, prefixSlice, tail, List.length_take, List.length_drop]
  rfl

private theorem initialize_parts (words : Slice U64) (budget : Usize) (bound : budget.val < words.length) :
    (RebuiltLfsrRuntime.inclusive U64).index_mut ⟨budget⟩ words =
      .ok (prefixSlice words (budget.val + 1), restorePrefix words) ∧
    core.slice.Slice.fill core.clone.CloneU64 (prefixSlice words (budget.val + 1)) 0#u64 =
      .ok (zeroWords (prefixSlice words (budget.val + 1))) ∧
    Slice.update (restorePrefix words (zeroWords (prefixSlice words (budget.val + 1)))) 0#usize 1#u64 =
      .ok (initialBuffer words budget) := by
  refine ⟨inclusive_prefix words budget bound, fill_zero _, ?_⟩
  exact Reconstruction.update_normal _ _ _ (by rw [restore_length]; change 0 < words.length; omega)

theorem entry_refines : ActualBmEntryRefines := by
  intro K kernels syndromes capacity budget buffers meter admitted
  have priced := BmPrice.bm_price_refines budget
  cases cost : WorkSchedule.checkedCost (BmPrice.bmUnits budget) with
  | Err error =>
    simp [locator, priced, cost, expectedEntry, pricing, StageCharge.chargeResult,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  | Ok amount =>
    have charge := StageCharge.meter_charge_refines meter amount
    cases charged : StageCharge.chargeResult meter (.Ok amount) with
    | mk result finalMeter =>
      rw [charged] at charge
      cases result with
      | Err error =>
        simp [locator, priced, cost, charge, expectedEntry, pricing, charged,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
      | Ok empty =>
        cases empty
        have ready : (pricing meter budget).1 = .Ok () := by simp [pricing, cost, charged]
        obtain ⟨budgetBound, bufferBound⟩ := admitted ready
        have upper := Slice.length_ineq buffers
        change buffers.length ≤ Usize.max at upper
        obtain ⟨width, plus, widthValue⟩ := RawMulTable.normal_of_spec _ _
          (Usize.add_spec (x := capacity) (y := 1#usize)
            (by change capacity.val + 1 ≤ Usize.max; omega))
        change width.val = capacity.val + 1 at widthValue
        let rest := tail buffers width.val
        let rest1 := tail rest width.val
        have restLen : rest.length = buffers.length - width.val := tail_length _ _
        have rest1Len : rest1.length = buffers.length - width.val - width.val := by
          change (tail rest width.val).length = _
          rw [tail_length, restLen]
        have split0 := split_refines buffers width (by omega)
        have split1 := split_refines rest width (by omega)
        have split2 := split_refines rest1 width (by omega)
        have connectionLen : (prefixSlice buffers width.val).length = width.val := by
          rw [prefix_length, Nat.min_eq_left (by omega)]
        have previousLen : (prefixSlice rest width.val).length = width.val := by
          rw [prefix_length, Nat.min_eq_left (by omega)]
        obtain ⟨prefix0, fill0, update0⟩ :=
          initialize_parts (prefixSlice buffers width.val) budget (by omega)
        obtain ⟨prefix1, fill1, update1⟩ :=
          initialize_parts (prefixSlice rest width.val) budget (by omega)
        have amountValue := ((WorkSchedule.checked_cost_ok_iff _ _).mp cost).2
        have amountWord : amount = (⟨BitVec.ofNat 64 (BmPrice.bmUnits budget)⟩ : U64) := by
          apply UScalar.eq_of_val_eq
          have room := ((WorkSchedule.checked_cost_ok_iff _ _).mp cost).1
          rw [amountValue]
          change _ = (BitVec.ofNat 64 (BmPrice.bmUnits budget)).toNat
          rw [BitVec.toNat_ofNat]
          rw [U64.max_eq] at room
          exact (Nat.mod_eq_of_lt (by omega)).symm
        simp only [locator, priced, cost, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, charge, plus,
          expectedEntry, pricing, charged]
        dsimp! only
        rw [split0]
        simp only [Bind.bind, bind_ok]
        dsimp! only
        rw [split1]
        simp only [Bind.bind, bind_ok]
        dsimp! only
        rw [split2]
        simp only [Bind.bind, bind_ok]
        dsimp! only
        simp only [core.slice.index.Slice.index_mut, prefix0, bind_ok]
        dsimp! only
        simp only [fill0, bind_ok, prefix1]
        dsimp! only
        simp only [fill1, bind_ok, update0, update1]
        rw [amountWord]

end BulksketchBridge.BmEntry
