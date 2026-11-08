import BulksketchBridge.BmAcceptedSpec
import BulksketchBridge.BmEvenStep

namespace BulksketchBridge.BmAccepted

open Aeneas Aeneas.Std BmDiscrepancy BmStepControl BmEvenStep DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.bm bulksketch.types

open Aeneas.Std.WP

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

private theorem copy_prefix_refines (destination source : Slice U64) (len : Usize)
    (destinationBound : len.val ≤ destination.length) (sourceBound : len.val ≤ source.length) :
    copyPrefix destination source len = .ok (destination.setSlice! 0 (prefixSlice source len.val).val) := by
  have sameLength : (prefixSlice destination len.val).length = (prefixSlice source len.val).length := by
    rw [prefix_length, prefix_length, Nat.min_eq_left destinationBound, Nat.min_eq_left sourceBound]
  unfold copyPrefix
  simp only [Slice.index_mut_SliceIndexRangeToUsizeSliceInst,
    prefix_normal destination len destinationBound, Slice.index_SliceIndexRangeToUsizeSliceInst,
    shared_prefix_normal source len sourceBound, bind_ok]
  change Aeneas.Std.bind (core.slice.Slice.copy_from_slice core.marker.CopyU64
    (prefixSlice destination len.val) (prefixSlice source len.val))
    (fun copied => .ok (restorePrefix destination copied)) = _
  rw [ClosedLeaf.copy_normal _ _ sameLength, bind_ok]
  rfl

private theorem copy_growth_frames (connection previous saved : Slice U64) (len : Usize)
    (connectionBound : len.val ≤ connection.length) (previousBound : len.val ≤ previous.length)
    (savedBound : len.val ≤ saved.length) :
    (do
      let saved1 ← copyPrefix saved connection len
      let previous1 ← copyPrefix previous saved1 len
      pure (saved1, previous1)) =
      .ok (saved.setSlice! 0 (prefixSlice connection len.val).val,
        previous.setSlice! 0 (prefixSlice connection len.val).val) := by
  have savedBound' : len.val ≤ (saved.setSlice! 0 (prefixSlice connection len.val).val).length := by
    rw [Slice.setSlice!_length]
    exact savedBound
  have takeEq :
      prefixSlice (saved.setSlice! 0 (prefixSlice connection len.val).val) len.val =
        prefixSlice connection len.val := by
    apply Slice.ext
    have payloadLen : (prefixSlice connection len.val).val.length = len.val :=
      (prefix_length _ _).trans (Nat.min_eq_left connectionBound)
    simp only [prefixSlice, Slice.from_val] at payloadLen ⊢
    rw [Slice.setSlice!_val, List.setSlice!]
    simp only [List.take_zero, List.nil_append, Nat.sub_zero, Nat.zero_add, payloadLen]
    rw [Nat.min_eq_left savedBound]
    simp only [List.take_take, Nat.min_self]
    exact List.take_append_of_le_length (by omega) |>.trans (by rw [List.take_take, Nat.min_self])
  change Aeneas.Std.bind (copyPrefix saved connection len) (fun saved1 =>
    Aeneas.Std.bind (copyPrefix previous saved1 len) (fun previous1 => .ok (saved1, previous1))) = _
  rw [copy_prefix_refines saved connection len savedBound connectionBound, bind_ok,
    copy_prefix_refines previous _ len previousBound savedBound', bind_ok, takeEq]

local macro "factor_update" growth:term : tactic =>
  `(tactic| (
    by_cases grow : $growth <;>
      simp only [acceptedTail, BmConnectionUpdate.run, copyPrefix,
        grow, ite_true, ite_false, core.ops.range.RangeInclusive.new, Aeneas.Std.bind_assoc, bind_ok] <;>
      repeat' first
        | rfl
        | (congr 1; funext input
           first | (have _ : _ × _ := input; cases input) | skip
           try dsimp! only
           try simp only [Aeneas.Std.bind_assoc, bind_ok])))

theorem accepted_tail_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (raw : RawArithmetic kernels) (reduce : ReduceArithmetic kernels)
    (back0 back1 back2 : BmTerminal.Back) (tail syndromes : Slice U64)
    (budget : Usize) (cost : WorkUnits) (iter : IndexRange) (meter finalMeter : WorkMeter)
    (connection previous saved : Slice U64) (degree previousLen shift : Usize) (previousDelta : U64)
    (active : iter.start.val < iter.«end».val) (even : iter.start.val % 2 = 0)
    (bounds : PreludeBounds connection syndromes degree iter.start)
    (charged : stepCharge iter.start meter cost = (.Ok (), finalMeter))
    (nonzero : deltaWord connection syndromes degree iter.start ≠ 0#u64)
    (twiceFits : 2 * degree.val ≤ Usize.max) (within : nextDegree degree iter.start ≤ budget.val) :
    ∃ candidate : Usize, candidate.val = nextDegree degree iter.start ∧
      locator_loop0.body fieldDictionary kernels back0 back1 tail back2 syndromes budget cost iter meter
        connection previous saved degree previousLen shift previousDelta =
      acceptedTail kernels (nextRange iter) finalMeter connection previous saved degree candidate previousLen shift
        previousDelta (deltaWord connection syndromes degree iter.start) (2 * degree.val ≤ iter.start.val) := by
  obtain ⟨first, last, prelude⟩ := prelude_refines kernels raw reduce connection syndromes degree iter.start bounds
  obtain ⟨twice, candidate, doubled, twiceVal, candidateNormal, candidateVal⟩ :=
    degree_candidate_refines degree iter.start last first twiceFits prelude.nextIndex prelude.firstIndex prelude.firstVal
  simp only [prelude.nextIndex, prelude.firstIndex, bind_ok] at candidateNormal
  have accepts : ¬ budget < candidate := by rw [UScalar.lt_equiv, candidateVal]; omega
  have grows : (twice ≤ iter.start) ↔ 2 * degree.val ≤ iter.start.val := by rw [UScalar.le_equiv, twiceVal]
  simp only [grows] at candidateNormal
  have parity := even_test iter.start even
  refine ⟨candidate, candidateVal, ?_⟩
  by_cases initial : iter.start = 0#usize
  · have test : (iter.start != 0#usize) = false := by simp [initial]
    have sameMeter : finalMeter = meter := by
      have exactMeter := congrArg Prod.snd charged
      simpa [stepCharge, initial] using exactMeter.symm
    simp only [locator_loop0.body, next_active iter active, bind_ok]
    dsimp! only
    simp only [test, Bool.false_eq_true, ite_false, parity, bind_ok, ite_true,
      prelude.coefficients, core.slice.Slice.iter, prelude.nextIndex, prelude.firstIndex,
      core.ops.range.RangeInclusive.new, prelude.moments,
      core.iter.traits.iterator.Iterator.rev.trait_default, core.iter.traits.iterator.Iterator.rev.default,
      core.iter.traits.iterator.Iterator.zip.trait_default, core.iter.traits.iterator.Iterator.zip.default,
      core.iter.traits.collect.IntoIterator.Blanket.into_iter]
    have computed := prelude.firstLoop
    simp only [sourceZip, zipAt] at computed
    simp only [computed, bind_ok]
    dsimp! only
    simp only [prelude.reduced, bind_ok, nonzero, ite_false, doubled, candidateNormal, accepts, sameMeter, grows]
    factor_update (2 * degree.val ≤ iter.start.val)
  · have test : (iter.start != 0#usize) = true := by simp [initial]
    have charge : meter.charge cost = .ok (.Ok (), finalMeter) := by
      rw [StageCharge.meter_charge_refines]
      simpa only [stepCharge, initial, ite_false] using congrArg Result.ok charged
    simp only [locator_loop0.body, next_active iter active, bind_ok]
    dsimp! only
    simp only [test, ite_true, charge, bind_ok]
    dsimp! only
    simp only [bind_ok, parity, ite_true,
      prelude.coefficients, core.slice.Slice.iter, prelude.nextIndex, prelude.firstIndex,
      core.ops.range.RangeInclusive.new, prelude.moments,
      core.iter.traits.iterator.Iterator.rev.trait_default, core.iter.traits.iterator.Iterator.rev.default,
      core.iter.traits.iterator.Iterator.zip.trait_default, core.iter.traits.iterator.Iterator.zip.default,
      core.iter.traits.collect.IntoIterator.Blanket.into_iter]
    have computed := prelude.paidLoop
    simp only [sourceZip, zipAt] at computed
    simp only [computed, bind_ok]
    dsimp! only
    simp only [prelude.reduced, bind_ok, nonzero, ite_false, doubled, candidateNormal, accepts, grows]
    factor_update (2 * degree.val ≤ iter.start.val)

theorem accepted_tail_frames {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : BmMutable.NativeMul kernels) (next : IndexRange) (meter : WorkMeter)
    (connection previous saved : Slice U64) (degree candidate index len previousLen shift : Usize)
    (previousDelta delta : U64) (candidateVal : candidate.val = nextDegree degree index)
    (lenNormal : (degree + 1#usize : Result Usize) = .ok len) (lenVal : len.val = degree.val + 1)
    (prefixFits : len.val ≤ connection.length)
    (bounds : UpdateBounds connection previous saved degree index shift previousLen) :
    acceptedTail kernels next meter connection previous saved degree candidate previousLen shift
      previousDelta delta (2 * degree.val ≤ index.val) =
    .ok (.cont (expectedAccepted next meter connection previous saved degree candidate len previousLen shift
      previousDelta delta (2 * degree.val ≤ index.val))) := by
  have candidateFits : candidate.val < connection.length := candidateVal ▸ bounds.candidate
  have gapOrdered : len.val ≤ candidate.val + 1 := by
    rw [lenVal, candidateVal, nextDegree]
    split <;> omega
  have updated := BmConnectionUpdate.connection_update_refines kernels mul connection previous
    len candidate shift previousLen previousDelta delta prefixFits gapOrdered candidateFits bounds.shifted bounds.previousRead
  by_cases grows : 2 * degree.val ≤ index.val
  · obtain ⟨previousBound, savedBound⟩ := bounds.growthCopies grows
    rw [← lenVal] at previousBound savedBound
    have saveNormal := copy_prefix_refines saved connection len savedBound prefixFits
    let saved1 := saved.setSlice! 0 (DenseCoefficient.prefixSlice connection len.val).val
    have saved1Bound : len.val ≤ saved1.length := by
      simp only [saved1, Slice.setSlice!_length]
      exact savedBound
    have previousNormal := copy_prefix_refines previous saved1 len previousBound saved1Bound
    have copyFrames := copy_growth_frames connection previous saved len
      prefixFits previousBound savedBound
    change copyPrefix saved connection len = Result.ok saved1 at saveNormal
    change Aeneas.Std.bind (copyPrefix saved connection len) (fun row =>
      Aeneas.Std.bind (copyPrefix previous row len)
        (fun prior => .ok (row, prior))) = _ at copyFrames
    rw [saveNormal, bind_ok, previousNormal, bind_ok] at copyFrames
    have previousEq := congrArg Prod.snd (Result.ok_injective copyFrames)
    change previous.setSlice! 0 (DenseCoefficient.prefixSlice saved1 len.val).val =
      previous.setSlice! 0 (DenseCoefficient.prefixSlice connection len.val).val at previousEq
    simp only [acceptedTail, lenNormal, bind_ok, grows, ite_true, saveNormal, updated,
      previousNormal, previousEq, expectedAccepted]
    rfl
  · simp only [acceptedTail, lenNormal, bind_ok, grows, ite_false, updated,
      shift_increment shift (bounds.incrementShift grows), expectedAccepted]

theorem accepted_update_refines : ActualBmAcceptedUpdate := by
  intro K kernels raw reduce mul back0 back1 back2 tail syndromes budget cost iter meter finalMeter
    connection previous saved degree previousLen shift previousDelta active even bounds charged nonzero
    twiceFits within updateBounds
  obtain ⟨candidate, candidateVal, tailNormal⟩ := accepted_tail_refines kernels raw reduce back0 back1 back2
    tail syndromes budget cost iter meter finalMeter connection previous saved degree previousLen shift
    previousDelta active even bounds charged nonzero twiceFits within
  have prefixFits : degree.val + 1 ≤ connection.length := Nat.succ_le_of_lt bounds.connection
  obtain ⟨len, lenNormal, lenVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := degree) (y := 1#usize) (prefixFits.trans connection.length_ineq))
  change len.val = degree.val + 1 at lenVal
  refine ⟨candidate, len, candidateVal, lenVal, tailNormal.trans ?_⟩
  exact accepted_tail_frames kernels mul (nextRange iter) finalMeter connection previous saved degree candidate
    iter.start len previousLen shift previousDelta (deltaWord connection syndromes degree iter.start) candidateVal
    lenNormal lenVal (lenVal ▸ prefixFits) updateBounds

end BulksketchBridge.BmAccepted
