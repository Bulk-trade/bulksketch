import BulksketchBridge.BmLocatorSpec
import BulksketchBridge.BmLoop
import BulksketchBridge.BmEntry

namespace BulksketchBridge.BmLocator

open Aeneas Aeneas.Std BmLoop BmEntry DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem initial_admitted (syndromes buffers : Slice U64) (capacity budget : Usize) (meter : WorkMeter)
    (budgetBound : budget.val ≤ capacity.val) (bufferBound : 3 * (capacity.val + 1) ≤ buffers.length)
    (syndromeBound : 2 * capacity.val + 1 ≤ syndromes.length) :
    Admitted (inputs syndromes buffers capacity budget) (initial buffers capacity budget meter) := by
  have inputMax : syndromes.length ≤ Usize.max := syndromes.length_ineq
  have endVal := ClosedLeafAdvance.word_val (2 * capacity.val) (by omega)
  have firstLen (row : Slice U64) (room : capacity.val + 1 ≤ row.length) :
      (prefixSlice row (capacity.val + 1)).length = capacity.val + 1 := by
    rw [prefix_length, Nat.min_eq_left room]
  have initializedLen (row : Slice U64) : (initialBuffer row budget).length = row.length := by
    rw [initialBuffer, Slice.setAtNat_length, restore_length]
  simp only [Admitted, initial, inputs, endVal, initializedLen]
  have restRoom : capacity.val + 1 ≤ (BmEntry.tail buffers (capacity.val + 1)).length := by
    rw [tail_length]
    omega
  have savedRoom : capacity.val + 1 ≤
      (BmEntry.tail (BmEntry.tail buffers (capacity.val + 1)) (capacity.val + 1)).length := by
    rw [tail_length, tail_length]
    omega
  rw [firstLen buffers (by omega), firstLen _ restRoom, firstLen _ savedRoom]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  simpa only [show (0#usize).val = 0 by simp, show (1#usize).val = 1 by simp] using
    BmScalar.initial budget.val

theorem locator_refines : ActualBmLocator := by
  intro K kernels raw reduce mul inverse syndromes capacity budget buffers meter admitted
  rw [entry_refines kernels syndromes capacity budget buffers meter
    (fun charged => ⟨(admitted charged).1, (admitted charged).2.1⟩)]
  cases priced : pricing meter budget with
  | mk payment finalMeter =>
    cases payment with
    | Err error =>
      exact ⟨(.Err error, buffers, finalMeter),
        by simp only [result, priced], by simp only [expectedEntry, priced]; rfl⟩
    | Ok paidUnit =>
      cases paidUnit
      obtain ⟨budgetBound, bufferBound, syndromeBound⟩ := admitted (by simp only [priced])
      have inputMax : syndromes.length ≤ Usize.max := syndromes.length_ineq
      have widthFits : capacity.val + 1 ≤ Usize.max := by omega
      have twiceFits : 2 * capacity.val ≤ Usize.max := by omega
      obtain ⟨width, plus, widthVal⟩ := RawMulTable.normal_of_spec _ _
        (Usize.add_spec (x := capacity) (y := 1#usize) (by exact widthFits))
      obtain ⟨stop, doubled, stopVal⟩ := RawMulTable.normal_of_spec _ _
        (Usize.mul_spec (x := 2#usize) (y := capacity) (by exact twiceFits))
      change width.val = capacity.val + 1 at widthVal
      change stop.val = 2 * capacity.val at stopVal
      have stopEq : stop = ClosedLeafAdvance.usizeWord (2 * capacity.val) := by
        apply UScalar.eq_of_val_eq
        rw [stopVal, ClosedLeafAdvance.word_val _ twiceFits]
      let input := inputs syndromes buffers capacity budget
      let start := initial buffers capacity budget finalMeter
      have valid : Admitted input start := initial_admitted syndromes buffers capacity budget finalMeter
        budgetBound bufferBound syndromeBound
      have remaining : 2 * capacity.val = start.1.«end».val - start.1.start.val := by
        simp only [start, initial, ClosedLeafAdvance.word_val _ twiceFits, show (0#usize).val = 0 by simp,
          Nat.sub_zero]
      obtain ⟨last, reply, modeled, native⟩ := run_refines kernels raw reduce mul inverse input start
        (2 * capacity.val) valid remaining
      refine ⟨reply, ?_, ?_⟩
      · simp only [result, priced]
        change (run input (2 * capacity.val) start).map Prod.snd = _
        rw [modeled]
        rfl
      · simp only [expectedEntry, priced, plus, doubled, bind_ok, widthVal, stopEq]
        exact native

end BulksketchBridge.BmLocator
