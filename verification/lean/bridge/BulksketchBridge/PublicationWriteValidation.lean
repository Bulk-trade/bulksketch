import BulksketchBridge.PublicationWrite

namespace BulksketchBridge.PublicationWrite

open Aeneas Aeneas.Std Result Error
open Aeneas.Std.PublicationWriteRuntime Aeneas.Std.CanonicalizeRuntime
open bulksketch.sketch.api bulksketch.sketch.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

def ActualPublicationWriteRowRejects : Prop :=
  ∀ (before : Publication) (bucket : Usize) (outcome : DecodeOutcome) (zero : Bool),
    ¬ (before.failure = none ∧ bucket = before.written ∧ bucket < before.rows) →
    Publication.write before bucket outcome zero = .fail .assertionFailure

theorem write_invalid_row : ActualPublicationWriteRowRejects := by
  intro before bucket outcome zero invalid
  cases failure : before.failure with
  | some error =>
    simp [Publication.write, failure, massert, bind_fail]
  | none =>
    by_cases ordered : bucket = before.written
    · have out : ¬bucket < before.rows := fun within => invalid ⟨failure, ordered, within⟩
      subst bucket
      simp [Publication.write, failure, massert, out, bind_ok, bind_fail]
    · simp [Publication.write, failure, massert, ordered, bind_ok, bind_fail]

def ActualPublicationWriteDecodedRejects : Prop :=
  ∀ (before : Publication) (bucket : Usize) (ids : Slice U64) (zero : Bool),
    (ids.val = [] ∧ zero = false) ∨ ids.val.head? = some 0#u64 ∨ ascendingWindows ids = false →
    Publication.write before bucket (.Decoded ids) zero = .fail .assertionFailure

private theorem zero_head (ids : Slice U64) (head : ids.val.head? = some 0#u64) :
    core.cmp.PartialEq.ne.trait_default (optionCmp (core.cmp.PartialEqShared core.cmp.PartialEqU64))
      ids.val.head? (some 0#u64) = .ok false := by
  simp [head, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, optionCmp,
    ExecutionDriverRuntime.optionEq, core.cmp.PartialEqShared, core.cmp.impls.PartialEqShared.eq,
    core.cmp.PartialEqU64, core.cmp.impls.PartialEqU64.eq, liftFun2, bind_ok]

theorem write_invalid_decoded : ActualPublicationWriteDecodedRejects := by
  intro before bucket ids zero rejected
  by_cases admission : before.failure = none ∧ bucket = before.written ∧ bucket < before.rows
  · obtain ⟨clear, ordered, within⟩ := admission
    subst bucket
    have emptyNormal : core.slice.Slice.is_empty ids = .ok ids.val.isEmpty := by
      unfold core.slice.Slice.is_empty
      simp only [Slice.len_val, Slice.length, List.length_eq_zero_iff]
      cases ids.val <;> rfl
    by_cases words : ids.val = []
    · rcases rejected with ⟨_, noZero⟩ | head | windowsRejected
      · simp [Publication.write, clear, within, massert, emptyNormal, words, noZero, bind_ok, bind_fail]
      · simp [words] at head
      · simp [ascendingWindows, BulksketchBridge.CanonicalizeOrdering.pairWindows, words] at windowsRejected
    · have notEmpty : ids.val.isEmpty = false := by simpa using words
      rcases rejected with ⟨empty, _⟩ | head | windowsRejected
      · exact (words empty).elim
      · have eq := zero_head ids head
        cases zero <;>
          simp [Publication.write, clear, within, massert, emptyNormal, notEmpty,
            PublicationWriteRuntime.first, eq, bind_ok, bind_fail, words]
      · by_cases head : ids.val.head? = some 0#u64
        · have eq := zero_head ids head
          cases zero <;>
            simp [Publication.write, clear, within, massert, emptyNormal, notEmpty,
              PublicationWriteRuntime.first, eq, bind_ok, bind_fail, words]
        · have firstNormal := nonzero_head ids head
          obtain ⟨_, allNormal⟩ := window_check ids
          cases zero <;>
            simp [Publication.write, clear, within, massert, emptyNormal, notEmpty,
              PublicationWriteRuntime.first, firstNormal, CanonicalizeRuntime.windows, allNormal,
              windowsRejected, bind_ok, bind_fail, words]
  · exact write_invalid_row before bucket (.Decoded ids) zero admission

#print axioms write_invalid_row
#print axioms write_invalid_decoded

end BulksketchBridge.PublicationWrite
