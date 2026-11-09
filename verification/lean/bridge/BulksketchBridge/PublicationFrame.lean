import Arithmetic.PublicationFrameGenerated
import BulksketchBridge.RawMulTable
import BulksketchBridge.DenseMulSpec

namespace BulksketchBridge.PublicationFrame

open Aeneas Aeneas.Std Aeneas.Std.WP
open bulksketch.sketch.api bulksketch.sketch.scratch bulksketch.types

set_option maxRecDepth 4096

def unset : StoredOutcome := ⟨.Unset, 0#u64, 0#u64⟩

def initialized (results : ResultStorage) (layout : ScratchLayout) : Publication :=
  { results := { results with outcomes := results.outcomes.setSlice! 0 (List.replicate layout.outcomes.val unset) }
    rows := layout.outcomes
    written := 0#usize
    used_ids := 0#usize
    id_capacity := layout.result_ids
    failure := none }

/-- Exact result storage and backward borrow of the original constructor. -/
def ActualPublicationNew : Prop :=
  ∀ (results : ResultStorage) (layout : ScratchLayout),
    layout.result_ids.val ≤ results.ids.length → layout.outcomes.val ≤ results.outcomes.length →
    Publication.new results layout = .ok (initialized results layout, Publication.results)

theorem new_refines : ActualPublicationNew := by
  intro results layout idRoom outcomeRoom
  obtain ⟨⟨part, back⟩, cut, _, length, restored⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec
      ⟨layout.outcomes⟩ results.outcomes outcomeRoom)
  have default : StoredOutcome.Insts.CoreDefaultDefault.default = .ok unset := by
    simp only [StoredOutcome.Insts.CoreDefaultDefault.default,
      OutcomeStatus.Insts.CoreDefaultDefault.default, bind_ok]
    rfl
  obtain ⟨filled, written, _, words⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.Slice.fill.spec StoredOutcome.Insts.CoreCloneClone part unset
      (by simp [StoredOutcome.Insts.CoreCloneClone.clone, spec_ok]))
  have updated : back filled = (initialized results layout).results.outcomes := by
    apply Slice.ext
    rw [restored filled, words, length]
    simp only [initialized, Slice.setSlice!_val]
  have idsLen : layout.result_ids ≤ Slice.len results.ids := idRoom
  have outLen : layout.outcomes ≤ Slice.len results.outcomes := outcomeRoom
  simp only [Publication.new, ge_iff_le, idsLen, outLen, massert, ite_true,
    Slice.index_mut_SliceIndexRangeToUsizeSliceInst, cut, default, bind_ok]
  dsimp! only
  rw [written, bind_ok, updated]
  rfl

def ActualPublicationFail : Prop :=
  ∀ (before : Publication) (error : DecodeError),
    Publication.fail before error =
      .ok ({ before with failure := some (before.failure.getD error) },
        fun later => { before with results := later.results })

theorem fail_refines : ActualPublicationFail := by
  intro before error
  rcases before with ⟨results, rows, written, used, cap, failure⟩
  cases failure <;> rfl

def expectedFinish (self : Publication) (work : WorkUnits) (peak : Usize) :
    Result (core.result.Result DecodeReport DecodeError × Publication) :=
  match self.failure with
  | some error => .ok (.Err error, self)
  | none =>
    if self.written = self.rows ∧ self.rows.val ≤ self.results.outcomes.length ∧
        self.used_ids.val ≤ self.results.ids.length then
      .ok (.Ok { outcomes := DenseMul.takeSlice self.results.outcomes self.rows.val
                 ids := DenseMul.takeSlice self.results.ids self.used_ids.val
                 work := work
                 peak_scratch_bytes := peak }, self)
    else .fail .panic

/-- The original report lends only committed prefixes. A request failure
returns the first error even if completion counters or slice sizes are invalid. -/
def ActualPublicationFinish : Prop :=
  ∀ (self : Publication) (work : WorkUnits) (peak : Usize),
    Publication.finish self work peak = expectedFinish self work peak

theorem finish_refines : ActualPublicationFinish := by
  intro self work peak
  cases failed : self.failure with
  | some error => simp only [Publication.finish, expectedFinish, failed]
  | none =>
    by_cases complete : self.written = self.rows
    · by_cases rows : self.rows.val ≤ self.results.outcomes.length <;>
        by_cases ids : self.used_ids.val ≤ self.results.ids.length <;>
        simp [Publication.finish, expectedFinish, failed, complete, rows, ids,
          core.slice.index.SliceIndexRangeToUsizeSlice.index, DenseMul.takeSlice,
          List.slice_zero_j, bind_ok, bind_fail]
    · simp only [Publication.finish, expectedFinish, failed, complete, ite_false, false_and,
        core.fmt.Arguments.from_str]
      change Aeneas.Std.bind (Result.ok ()) (fun _ => Result.fail .panic) = _
      rw [bind_ok]

def ActualPublicationNewRejects : Prop :=
  ∀ (results : ResultStorage) (layout : ScratchLayout),
    results.ids.length < layout.result_ids.val ∨ results.outcomes.length < layout.outcomes.val →
    Publication.new results layout = .fail .assertionFailure

theorem new_rejects : ActualPublicationNewRejects := by
  intro results layout insufficient
  by_cases ids : layout.result_ids ≤ Slice.len results.ids
  · have idRoom : layout.result_ids.val ≤ results.ids.length := by
      rw [← Slice.len_val]
      exact ids
    have outcomes : ¬ layout.outcomes ≤ Slice.len results.outcomes := by
      have short : results.outcomes.length < layout.outcomes.val := insufficient.resolve_left (by omega)
      intro enough
      have length : layout.outcomes.val ≤ results.outcomes.length := by rwa [← Slice.len_val]
      omega
    simp only [Publication.new, ge_iff_le, massert, ids, outcomes, ite_true, ite_false, bind_ok, bind_fail]
  · simp only [Publication.new, ge_iff_le, massert, ids, ite_false, bind_fail]

/-- The first original failure remains the returned error after the
original finalizer, even when some rows were previously stored. -/
def ActualPublicationFailedFinish : Prop :=
  ∀ (before : Publication) (error : DecodeError) (work : WorkUnits) (peak : Usize),
    (do
      let (failed, _) ← Publication.fail before error
      Publication.finish failed work peak) =
      .ok (.Err (before.failure.getD error),
        { before with failure := some (before.failure.getD error) })

theorem failed_finish_refines : ActualPublicationFailedFinish := by
  intro before error work peak
  rw [fail_refines before error, bind_tc_ok]
  dsimp! only

#print axioms new_refines
#print axioms fail_refines
#print axioms finish_refines
#print axioms new_rejects
#print axioms failed_finish_refines

end BulksketchBridge.PublicationFrame
