import BulksketchBridge.PublicationReadback

namespace BulksketchBridge.PublicationWrite

open Aeneas Aeneas.Std Result
open bulksketch.sketch.api bulksketch.types

/-- Select the original Equal or Failed outcome with the matching stored tag. -/
def statusOutcome (failure : Option DecodeFailure) : DecodeOutcome :=
  match failure with
  | none => .Equal
  | some reason => .Failed reason

def storedStatus (failure : Option DecodeFailure) : OutcomeStatus :=
  match failure with
  | none => .Equal
  | some reason => status reason

def ActualStatusPublicationReadback : Prop :=
  ∀ (before : Publication) (bucket : Usize) (reason : Option DecodeFailure) (zero : Bool)
    (work : WorkUnits) (peak : Usize),
    RowAdmission before bucket →
    before.rows.val = before.written.val + 1 →
    before.used_ids.val ≤ before.results.ids.length →
    ∃ (after : Publication) (report : DecodeReport),
      Publication.write before bucket (statusOutcome reason) zero = .ok (after, back before) ∧
      Publication.finish after work peak = .ok (.Ok report, after) ∧
      DecodeReport.outcome report bucket = .ok (some (statusOutcome reason)) ∧
      DecodeReport.bucket_count report = .ok before.rows ∧
      report.ids.val = before.results.ids.val.take before.used_ids.val ∧
      report.work = work ∧ report.peak_scratch_bytes = peak

theorem status_publication_readback : ActualStatusPublicationReadback := by
  intro before bucket reason zero work peak admitted last idRoom
  obtain ⟨next, nextVal, equal, failed⟩ := write_status_refines before bucket zero admitted
  let after := appendStatus before bucket next (storedStatus reason)
  let report := committedReport after work peak
  let stored : StoredOutcome := ⟨storedStatus reason, 0#u64, 0#u64⟩
  have written : Publication.write before bucket (statusOutcome reason) zero = .ok (after, back before) := by
    cases reason <;> first | exact equal | exact failed _
  have complete : after.written = after.rows := UScalar.eq_of_val_eq (nextVal.trans last.symm)
  have rows : before.rows.val ≤ before.results.outcomes.length := by
    have ordered := congrArg UScalar.val admitted.ordered
    have inStore := admitted.storage
    omega
  have rowRoom : after.rows.val ≤ after.results.outcomes.length := by
    simpa only [after, appendStatus, Slice.length, Slice.set_val_eq, List.length_set] using rows
  have finished := finish_committed after work peak admitted.noFailure complete rowRoom idRoom
  have read : DecodeReport.outcome report bucket = .ok (some (statusOutcome reason)) := by
    rw [DecodeReport.outcome_refines report bucket]
    have record : report.outcomes.val[bucket.val]? = some stored :=
      row_readback before.results.outcomes bucket before.rows stored admitted.room admitted.storage
    simp only [DecodeReport.expectedOutcome, record, DecodeReport.row, stored]
    cases reason with
    | none => rfl
    | some failure => cases failure <;> rfl
  have count : DecodeReport.bucket_count report = .ok before.rows := by
    rw [DecodeReport.bucket_count_refines report]
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [report, committedReport, DenseMul.takeSlice, Slice.len_val, Slice.length, Slice.from_val,
      List.length_take, Nat.min_eq_left rowRoom]
    rfl
  refine ⟨after, report, written, finished, read, count, ?_, rfl, rfl⟩
  simp only [report, committedReport, after, appendStatus, DenseMul.takeSlice, Slice.from_val]

#print axioms status_publication_readback

end BulksketchBridge.PublicationWrite
