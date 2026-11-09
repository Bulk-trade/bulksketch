import BulksketchBridge.PublicationStatusReadback

namespace BulksketchBridge.PublicationWrite

open Aeneas Aeneas.Std Result Algebra.Gf64 Polynomial
open ExecutionDriver RebuiltLfsr DenseCoefficient
open bulksketch.backend.contract bulksketch.decode.row bulksketch.decode.stages
open bulksketch.decode.scratch bulksketch.types bulksketch.sketch.api

set_option maxRecDepth 4096
set_option maxHeartbeats 3500000

def mayPublish (permits : U64 → Bool) (words : Slice U64) : Bool :=
  words.val.all fun word => decide (word ≠ 0#u64) && permits word

def publicationOutcome (permits : U64 → Bool) : RowResult → DecodeOutcome
  | .Equal => .Equal
  | .Failed reason => .Failed reason
  | .Decoded words =>
    if mayPublish permits words then .Decoded words else .Failed .InvalidLocator

def visibleRow (permits : U64 → Bool) (zero : Bool) (native : RowResult)
    (visible : DecodeOutcome) : Prop :=
  match native with
  | .Equal => visible = .Equal
  | .Failed reason => visible = .Failed reason
  | .Decoded words =>
    if mayPublish permits words then
      ∃ exposed : Slice U64, visible = .Decoded exposed ∧
        exposed.val = (if zero then [0#u64] else []) ++ words.val
    else visible = .Failed .InvalidLocator

/-- Complete the original last-row canonicalization, publish the admitted
outcome, and return precisely that row through the original public accessor.
The request's ID permission function is an explicit interface argument. -/
def ActualCanonicalPublicationReadback : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace)
    (meter finalMeter : WorkMeter) (locator : Polynomial Field) (zero : Bool)
    (before : Publication) (bucket : Usize) (permits : U64 → Bool) (work : WorkUnits) (peak : Usize),
    CanonicalAdmission (self := self) (workspace := workspace) (meter := meter)
      (finalMeter := finalMeter) (locator := locator) (zero := zero) →
    RowAdmission before bucket →
    before.rows.val = before.written.val + 1 →
    before.used_ids.val + self.budget.total.val ≤ before.id_capacity.val →
    before.used_ids.val + self.budget.total.val ≤ before.results.ids.length →
    let after := { self with state := .Complete }
    let written := canonicalWritten self workspace
    nativeCandidateDriver nativeCanonicalize kernels self input workspace meter =
      .ok (.Ok (progress .Canonicalization self), after, written, id, finalMeter) ∧
    (∀ point, locator.IsRoot point ↔
      ∃ word ∈ (prefixSlice written.roots self.roots.count.val).val, point = toField word.bv) ∧
    ∃ (native : RowResult) (committed : Publication) (report : DecodeReport) (visible : DecodeOutcome),
      Execution.completed_result RootSetup.gf64Dictionary kernels after written = .ok (.Ok native) ∧
      Publication.write before bucket (publicationOutcome permits native) zero =
        .ok (committed, back before) ∧
      Publication.finish committed work peak = .ok (.Ok report, committed) ∧
      DecodeReport.outcome report bucket = .ok (some visible) ∧
      DecodeReport.bucket_count report = .ok before.rows ∧
      visibleRow permits zero native visible ∧
      report.work = work ∧ report.peak_scratch_bytes = peak

theorem canonical_publication_readback : ActualCanonicalPublicationReadback := by
  intro K kernels self input workspace meter finalMeter locator zero before bucket permits work peak
    canonical admitted last cap storage after written
  obtain ⟨ran, roots, outcome⟩ :=
    canonical_publication_admission kernels self input workspace meter finalMeter locator zero canonical
  refine ⟨ran, roots, ?_⟩
  have idRoom : before.used_ids.val ≤ before.results.ids.length := by omega
  by_cases equal : self.roots.count = 0#usize ∧ self.budget.total = self.budget.nonzero
  · rw [ite_eq_left equal] at outcome
    obtain ⟨committed, report, wrote, finished, read, count, _, workExact, peakExact⟩ :=
      status_publication_readback before bucket none zero work peak admitted last idRoom
    exact ⟨.Equal, committed, report, .Equal, outcome.1, wrote, finished, read, count, rfl, workExact, peakExact⟩
  · rw [ite_eq_right equal] at outcome
    let words := prefixSlice written.roots self.roots.count.val
    obtain ⟨completed, _, valid, budget⟩ := outcome
    change zeroWidth zero + words.length ≤ self.budget.total.val at budget
    by_cases allowed : mayPublish permits words = true
    · obtain ⟨committed, report, exposed, wrote, finished, read, payload, countVal, workExact, peakExact⟩ :=
        decoded_publication_readback before bucket words zero work peak admitted valid last (by omega) (by omega)
      have count : DecodeReport.bucket_count report = .ok before.rows := by
        rw [DecodeReport.bucket_count_refines report, UScalar.eq_of_val_eq countVal]
      refine ⟨.Decoded words, committed, report, .Decoded exposed, completed, ?_, finished, read, count,
        ?_, workExact, peakExact⟩
      · simpa only [publicationOutcome, allowed, ite_true] using wrote
      · simp only [visibleRow, allowed, ite_true]
        exact ⟨exposed, rfl, payload⟩
    · obtain ⟨committed, report, wrote, finished, read, count, _, workExact, peakExact⟩ :=
        status_publication_readback before bucket (some .InvalidLocator) zero work peak admitted last idRoom
      refine ⟨.Decoded words, committed, report, .Failed .InvalidLocator, completed, ?_, finished,
        read, count, ?_, workExact, peakExact⟩
      · simpa only [publicationOutcome, statusOutcome, ite_eq_right allowed] using wrote
      · simp only [visibleRow, ite_eq_right allowed]

#print axioms canonical_publication_readback

end BulksketchBridge.PublicationWrite
