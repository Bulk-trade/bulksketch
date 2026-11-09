import BulksketchBridge.DecodeReport
import BulksketchBridge.NativePublicationAdmission
import BulksketchBridge.CandidateBucket

namespace BulksketchBridge.PublicationWrite

open Aeneas Aeneas.Std Result
open bulksketch.sketch.api bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def committedReport (after : Publication) (work : WorkUnits) (peak : Usize) : DecodeReport :=
  { outcomes := DenseMul.takeSlice after.results.outcomes after.rows.val
    ids := DenseMul.takeSlice after.results.ids after.used_ids.val
    work := work
    peak_scratch_bytes := peak }

private theorem finish_committed (after : Publication) (work : WorkUnits) (peak : Usize)
    (clear : after.failure = none) (complete : after.written = after.rows)
    (rowRoom : after.rows.val ≤ after.results.outcomes.length)
    (idRoom : after.used_ids.val ≤ after.results.ids.length) :
    Publication.finish after work peak = .ok (.Ok (committedReport after work peak), after) := by
  rw [PublicationFrame.finish_refines after work peak]
  simp only [PublicationFrame.expectedFinish, clear, complete, rowRoom, idRoom, true_and, ite_true]
  rfl

private theorem row_readback (outcomes : Slice StoredOutcome) (bucket rows : Usize)
    (entry : StoredOutcome) (row : bucket.val < rows.val) (inside : bucket.val < outcomes.length) :
    (DenseMul.takeSlice (outcomes.set bucket entry) rows.val).val[bucket.val]? = some entry := by
  simp only [DenseMul.takeSlice, Slice.from_val, Slice.set_val_eq, List.getElem?_take_of_lt row]
  exact List.getElem?_set_self (by exact inside)

private theorem window_payload (before : Slice U64) (used : Usize) (roots : Slice U64) (zero : Bool)
    (room : used.val + zeroWidth zero + roots.length ≤ before.length) :
    (ClosedLeaf.region
      ((withZero before used zero).setSlice! (used.val + zeroWidth zero) roots.val)
      used.val (used.val + zeroWidth zero + roots.length)).val =
        (if zero then [0#u64] else []) ++ roots.val := by
  have sameLength : (withZero before used zero).length = before.length := by
    cases zero <;> simp [withZero, Slice.set_val_eq, Slice.length]
  have insertRoom : used.val + zeroWidth zero ≤ (withZero before used zero).length := by
    rw [sameLength]
    omega
  have dataRoom : roots.val.length ≤ (withZero before used zero).val.length - (used.val + zeroWidth zero) := by
    change roots.length ≤ (withZero before used zero).length - (used.val + zeroWidth zero)
    rw [sameLength]
    omega
  simp only [ClosedLeaf.region, Slice.from_val, List.slice, Slice.setSlice!_val, List.setSlice!,
    Nat.min_eq_left dataRoom, List.take_length]
  have prefixLength : ((withZero before used zero).val.take (used.val + zeroWidth zero)).length =
      used.val + zeroWidth zero := by
    rw [List.length_take, Nat.min_eq_left insertRoom]
  rw [List.append_assoc, List.drop_append, prefixLength]
  cases zero with
  | false => simp [zeroWidth, List.length_take, Slice.length]
  | true =>
    have existing : used.val < before.length := by simp only [zeroWidth, ite_true] at room; omega
    have zeroAt : ((withZero before used true).val)[used.val]? = some 0#u64 := by
      simp only [withZero, ite_true, Slice.set_val_eq]
      exact List.getElem?_set_self (by exact existing)
    simp only [zeroWidth, ite_true, Nat.sub_eq_zero_of_le
      (Nat.le_succ _), List.drop_zero]
    have zeroPrefix : ((withZero before used true).val.take (used.val + 1)).drop used.val = [0#u64] := by
      rw [List.drop_take]
      simp only [Nat.add_sub_cancel_left]
      rw [List.take_one]
      rw [List.head?_drop, zeroAt]; rfl
    rw [zeroPrefix]
    rw [show used.val + 1 + roots.val.length - used.val = roots.val.length + 1 by omega]
    simp

/-- The original finalizer and public accessor expose the last admitted
decoded row as its exact zero prefix followed by its exact native roots. -/
def ActualDecodedPublicationReadback : Prop :=
  ∀ (before : Publication) (bucket : Usize) (roots : Slice U64) (zero : Bool)
    (work : WorkUnits) (peak : Usize),
    RowAdmission before bucket → validDecoded roots zero →
    before.rows.val = before.written.val + 1 →
    before.used_ids.val + zeroWidth zero + roots.length ≤ before.id_capacity.val →
    before.used_ids.val + zeroWidth zero + roots.length ≤ before.results.ids.length →
    ∃ (after : Publication) (report : DecodeReport) (decoded : Slice U64),
      Publication.write before bucket (.Decoded roots) zero = .ok (after, back before) ∧
      Publication.finish after work peak = .ok (.Ok report, after) ∧
      DecodeReport.outcome report bucket = .ok (some (.Decoded decoded)) ∧
      decoded.val = (if zero then [0#u64] else []) ++ roots.val ∧
      (report.outcomes.len).val = before.rows.val ∧
      report.work = work ∧ report.peak_scratch_bytes = peak

theorem decoded_publication_readback : ActualDecodedPublicationReadback := by
  intro before bucket roots zero work peak admitted valid last cap storage
  obtain ⟨endIds, next, count, endVal, nextVal, countVal, written⟩ :=
    write_decoded_refines before bucket roots zero admitted valid cap storage
  let after := decodedFrame before bucket endIds next count roots zero
  let report := committedReport after work peak
  let stored : StoredOutcome :=
    ⟨.Decoded, UScalar.cast .U64 before.used_ids, UScalar.cast .U64 count⟩
  let decoded := ClosedLeaf.region report.ids before.used_ids.val endIds.val
  have complete : after.written = after.rows :=
    UScalar.eq_of_val_eq (nextVal.trans last.symm)
  have rows : before.rows.val ≤ before.results.outcomes.length := by
    have ordered := congrArg UScalar.val admitted.ordered
    have inStore := admitted.storage
    omega
  have rowRoom : after.rows.val ≤ after.results.outcomes.length := by
    simpa only [after, decodedFrame, Slice.set_val_eq, Slice.length, List.length_set] using rows
  have idRoom : after.used_ids.val ≤ after.results.ids.length := by
    have withZeroLength :
        (withZero before.results.ids before.used_ids zero).length = before.results.ids.length := by
      cases zero <;> simp [withZero, Slice.set_val_eq, Slice.length]
    simpa only [after, decodedFrame, Slice.setSlice!_length, withZeroLength, endVal] using storage
  have finish := finish_committed after work peak admitted.noFailure complete rowRoom idRoom
  have recorded : report.outcomes.val[bucket.val]? = some stored :=
    row_readback before.results.outcomes bucket before.rows stored admitted.room admitted.storage
  have castExact (value : Usize) : (UScalar.cast .U64 value).val = value.val := by
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    exact CandidateNormalization.usize_fits_u64 value
  have countFits : count.val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    exact by simp only [Usize.max, Usize.numBits]; have bound := count.hBounds; omega
  have startFits : before.used_ids.val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    exact by simp only [Usize.max, Usize.numBits]; have bound := before.used_ids.hBounds; omega
  have sum : before.used_ids.val + count.val = endIds.val := by omega
  have endFits : endIds.val ≤ UScalar.max .Usize := by
    rw [UScalar.max_USize_eq]
    exact by simp only [Usize.max, Usize.numBits]; have bound := endIds.hBounds; omega
  have reportIds : report.ids.length = endIds.val := by
    simp only [report, committedReport, DenseMul.takeSlice, Slice.length, Slice.from_val, List.length_take]
    exact Nat.min_eq_left idRoom
  have read : DecodeReport.outcome report bucket = .ok (some (.Decoded decoded)) := by
    rw [DecodeReport.outcome_refines report bucket]
    simp only [DecodeReport.expectedOutcome, recorded, DecodeReport.row, stored, DecodeReport.decoded,
      castExact, sum, startFits, countFits, endFits, true_and, ite_true, reportIds, Nat.le_refl]
    rfl
  have payload : decoded.val = (if zero then [0#u64] else []) ++ roots.val := by
    change (ClosedLeaf.region (DenseMul.takeSlice after.results.ids endIds.val)
      before.used_ids.val endIds.val).val = _
    change (ClosedLeaf.region (DenseCoefficient.prefixSlice after.results.ids endIds.val)
      before.used_ids.val endIds.val).val = _
    rw [ClosedLeaf.region_prefix _ _ _ _ (Nat.le_refl _)]
    simp only [after, decodedFrame, endVal]
    exact window_payload before.results.ids before.used_ids roots zero storage
  refine ⟨after, report, decoded, written, finish, read, payload, ?_, rfl, rfl⟩
  simp only [report, committedReport, DenseMul.takeSlice, Slice.len_val, Slice.length, Slice.from_val,
    List.length_take, Nat.min_eq_left rowRoom]
  rfl

#print axioms decoded_publication_readback

end BulksketchBridge.PublicationWrite
