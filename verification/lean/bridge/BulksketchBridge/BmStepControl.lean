import BulksketchBridge.BmStepControlSpec
import BulksketchBridge.StageCharge
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.BmStepControl

open Aeneas Aeneas.Std Aeneas.Std.WP BmTerminal
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

set_option maxRecDepth 4096

theorem first_step_no_charge (meter : WorkMeter) (cost : WorkUnits) :
    stepCharge 0#usize meter cost = (.Ok (), meter) := rfl

private theorem incremented_eq (word value : Usize) (exactValue : word.val = value.val + 1) :
    word = incremented value := by
  apply Usize.bv_eq_imp_eq
  change word.bv = BitVec.ofNat _ (value.val + 1)
  rw [← exactValue, Usize.BitVec_ofNat_val]

theorem next_active (iter : IndexRange) (active : iter.start.val < iter.«end».val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      Result.ok (some iter.start, nextRange iter) := by
  obtain ⟨⟨option, next⟩, normal, optionEq, advanced, sameEnd⟩ := RawMulTable.normal_of_spec _ _
    (core.iter.range.IteratorRange.next_Usize_some_spec iter active)
  have exactNext : next = nextRange iter := by
    cases next with
    | mk start stop =>
      change start.val = iter.start.val + 1 at advanced
      change stop = iter.«end» at sameEnd
      simp only [nextRange, incremented_eq start iter.start advanced, sameEnd]
  rw [normal, optionEq, exactNext]

theorem shift_increment (shift : Usize) (fits : shift.val + 1 ≤ Usize.max) :
    (shift + 1#usize : Result Usize) = .ok (incremented shift) := by
  obtain ⟨word, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := shift) (y := 1#usize) (by exact fits))
  rw [normal, incremented_eq word shift exactWord]

theorem charge_failure_refines : ActualBmChargeFailure := by
  intro F K field kernels back0 back1 back2 tail syndromes budget cost iter meter finalMeter
    connection previous saved degree previousLen shift previousDelta error active charged
  have nonzero : iter.start ≠ 0#usize := by
    intro zero
    rw [zero, first_step_no_charge] at charged
    cases congrArg Prod.fst charged
  have nonzeroTest : (iter.start != 0#usize) = true := by simp [nonzero]
  have paid : meter.charge cost = Result.ok (.Err error, finalMeter) := by
    rw [StageCharge.meter_charge_refines]
    simpa only [stepCharge, nonzero, ite_false] using congrArg Result.ok charged
  simp only [locator_loop0.body, next_active iter active, bind_ok]
  dsimp! only
  simp only [nonzeroTest, ite_true, paid, bind_ok]
  dsimp! only
  simp only [bind_ok]
  dsimp! only
  simp only [core.convert.FromSame.from, Bind.bind, bind_ok, joinBuffers]

theorem odd_skip_refines : ActualBmOddSkip := by
  intro F K field kernels back0 back1 back2 tail syndromes budget cost iter meter finalMeter
    connection previous saved degree previousLen shift previousDelta active odd fits charged
  have nonzero : iter.start ≠ 0#usize := by
    intro zero
    rw [zero] at odd
    contradiction
  have nonzeroTest : (iter.start != 0#usize) = true := by simp [nonzero]
  have parity : core.num.Usize.is_multiple_of iter.start 2#usize = .ok false := by
    change Result.ok (iter.start.val % 2 == 0) = _
    rw [odd]
    rfl
  have paid : meter.charge cost = Result.ok (.Ok (), finalMeter) := by
    rw [StageCharge.meter_charge_refines]
    simpa only [stepCharge, nonzero, ite_false] using congrArg Result.ok charged
  simp only [locator_loop0.body, next_active iter active, bind_ok]
  dsimp! only
  simp only [nonzeroTest, ite_true, paid, bind_ok]
  dsimp! only
  simp only [bind_ok, parity, Bool.false_eq_true, ite_false, eq_self, shift_increment shift fits]

end BulksketchBridge.BmStepControl
