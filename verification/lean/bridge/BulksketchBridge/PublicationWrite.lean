import Arithmetic.PublicationWriteGenerated
import BulksketchBridge.PublicationFrame
import BulksketchBridge.RootDivideArithmetic

namespace BulksketchBridge.PublicationWrite

open Aeneas Aeneas.Std Result Error
open Aeneas.Std.PublicationWriteRuntime Aeneas.Std.CanonicalizeRuntime
open bulksketch.sketch.api bulksketch.sketch.scratch bulksketch.types
open BulksketchBridge.CanonicalizeOrdering

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

structure RowAdmission (before : Publication) (bucket : Usize) : Prop where
  noFailure : before.failure = none
  ordered : bucket = before.written
  room : bucket.val < before.rows.val
  storage : bucket.val < before.results.outcomes.length
  nextFits : before.written.val + 1 ≤ Usize.max

def back (before later : Publication) : Publication :=
  { before with results := later.results }

def status (reason : DecodeFailure) : OutcomeStatus :=
  match reason with
  | .DegreeExceedsBudget => .DegreeExceedsBudget
  | .InvalidLocator => .InvalidLocator
  | .NotSplit => .NotSplit
  | .VerificationFailed => .VerificationFailed

def appendStatus (before : Publication) (bucket : Usize) (next : Usize)
    (value : OutcomeStatus) : Publication :=
  let stored : StoredOutcome := ⟨value, 0#u64, 0#u64⟩
  { before with
    results := { before.results with outcomes := before.results.outcomes.set bucket stored }
    written := next }

def ActualPublicationWriteStatus : Prop :=
  ∀ before bucket zero, RowAdmission before bucket →
    ∃ next : Usize, next.val = before.written.val + 1 ∧
      Publication.write before bucket .Equal zero =
        .ok (appendStatus before bucket next .Equal, back before) ∧
      ∀ reason, Publication.write before bucket (.Failed reason) zero =
        .ok (appendStatus before bucket next (status reason), back before)

theorem write_status_refines : ActualPublicationWriteStatus := by
  intro before bucket zero admission
  obtain ⟨clear, ordered, row, storage, nextFits⟩ := admission
  subst bucket
  obtain ⟨next, normal, exactNext⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := before.written) (y := 1#usize) nextFits)
  have setOut (value : OutcomeStatus) :
      Slice.update before.results.outcomes before.written ⟨value, 0#u64, 0#u64⟩ =
        .ok (before.results.outcomes.set before.written ⟨value, 0#u64, 0#u64⟩) := by
    obtain ⟨written, ran, exact⟩ := RawMulTable.normal_of_spec _ _
      (Slice.update_spec before.results.outcomes before.written ⟨value, 0#u64, 0#u64⟩ storage)
    rw [ran, exact]
  have inside : before.written < before.rows := row
  refine ⟨next, exactNext, ?_, ?_⟩
  · simp [Publication.write, clear, inside, massert, bind_ok, setOut, normal, appendStatus]
    funext later
    simp [back, clear]
  · intro reason
    cases reason <;> simp [Publication.write, clear, inside, massert, bind_ok, setOut, normal, appendStatus, status]
    all_goals
      funext later
      simp [back, clear]

def ascendingWindows (ids : Slice U64) : Bool :=
  (pairWindows ids.val).all fun pair => decide (pair.1 < pair.2)

def validDecoded (ids : Slice U64) (zero : Bool) : Prop :=
  (ids.val ≠ [] ∨ zero = true) ∧ ids.val.head? ≠ some 0#u64 ∧ ascendingWindows ids = true

theorem window_predicate (left right : U64) :
    Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool.call_mut ()
      (pairSlice left right) = .ok (decide (left < right), ()) := by
  unfold Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool.call_mut
  simp [Slice.index_usize, pairSlice, Slice.from_val, bind_ok]

theorem window_check (ids : Slice U64) :
    ∃ unused, allWindows ()
        Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool
        ((pairWindows ids.val).map fun pair => pairSlice pair.1 pair.2) () =
      .ok (ascendingWindows ids, unused) := by
  let pred (word : Slice U64) := decide (word[0]! < word[1]!)
  let windows := (pairWindows ids.val).map fun pair => pairSlice pair.1 pair.2
  have law (item : Slice U64) (member : item ∈ windows) :
      Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool.call_mut
        () item = .ok (pred item, ()) := by
    obtain ⟨⟨left, right⟩, _, rfl⟩ := List.mem_map.mp member
    rw [show pred (pairSlice left right) = decide (left < right) by
      simp [pred, pairSlice, Slice.getElem!_Nat_eq]]
    exact window_predicate left right
  obtain ⟨consumed, ran⟩ := all_windows_exact
    Publication.write.closure_1.Insts.CoreOpsFunctionFnMutTupleShared1SliceU64Bool windows () pred law
  have exact : windows.all pred = ascendingWindows ids := by
    unfold windows ascendingWindows
    rw [List.all_map]
    rfl
  exact ⟨windows.drop consumed, exact ▸ ran⟩

theorem nonzero_head (ids : Slice U64) (good : ids.val.head? ≠ some 0#u64) :
    core.cmp.PartialEq.ne.trait_default (optionCmp (core.cmp.PartialEqShared core.cmp.PartialEqU64))
      ids.val.head? (some 0#u64) = .ok true := by
  cases head : ids.val.head? with
  | none =>
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      optionCmp, ExecutionDriverRuntime.optionEq, head, bind_ok]
  | some word =>
    have notZero : word ≠ 0#u64 := fun h => good (head.trans (congrArg some h))
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      optionCmp, ExecutionDriverRuntime.optionEq,
      core.cmp.PartialEqShared, core.cmp.impls.PartialEqShared.eq, core.cmp.PartialEqU64,
      core.cmp.impls.PartialEqU64.eq, liftFun2, head, notZero, bind_ok]

theorem read_at (ids : Slice U64) (i : Usize) (room : i.val < ids.length) :
    Slice.index_usize ids i = .ok ids[i.val]! := by
  obtain ⟨word, ran, exact⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec ids i room)
  rw [ran, exact, Slice.getElem!_Nat_eq, List.Inhabited_getElem_eq_getElem! _ _ room]

theorem write_at {T : Type} (words : Slice T) (i : Usize) (value : T) (room : i.val < words.length) :
    Slice.update words i value = .ok (words.set i value) := by
  obtain ⟨written, ran, exact⟩ := RawMulTable.normal_of_spec _ _ (Slice.update_spec words i value room)
  rw [ran, exact]

private theorem one_list {T : Type} (values : List T) (length : values.length = 1) :
    ∃ a, values = [a] := by
  cases values with
  | nil => simp at length
  | cons first rest =>
    cases rest with
    | nil => exact ⟨first, rfl⟩
    | cons _ _ => simp at length

private theorem two_list {T : Type} (values : List T) (length : values.length = 2) :
    ∃ a b, values = [a,b] := by
  cases values with
  | nil => simp at length
  | cons first rest =>
    cases rest with
    | nil => simp at length
    | cons second rest =>
      cases rest with
      | nil => exact ⟨first, second, rfl⟩
      | cons _ _ => simp at length

theorem one_copy (destination ids : Slice U64) (one : ids.length = 1)
    (room : destination.length = ids.length) :
    (do let word ← Slice.index_usize ids 0#usize
        Slice.update destination 0#usize word) = .ok ids := by
  simp only [Bind.bind, read_at ids 0#usize (by change 0 < ids.length; omega), bind_ok]
  rw [write_at destination 0#usize _ (by change 0 < destination.length; omega)]
  congr 1
  apply Slice.ext
  obtain ⟨a, input⟩ := one_list ids.val one
  obtain ⟨b, output⟩ := one_list destination.val (room.trans one)
  simp [Slice.set_val_eq, Slice.getElem!_Nat_eq, input, output]

theorem two_copy (destination ids : Slice U64) (two : ids.length = 2)
    (room : destination.length = ids.length) :
    (do let first ← Slice.index_usize ids 0#usize
        let second ← Slice.index_usize ids 1#usize
        let written ← Slice.update destination 0#usize first
        Slice.update written 1#usize second) = .ok ids := by
  simp only [Bind.bind, read_at ids 0#usize (by change 0 < ids.length; omega),
    read_at ids 1#usize (by change 1 < ids.length; omega), bind_ok]
  rw [write_at destination 0#usize _ (by change 0 < destination.length; omega), bind_ok]
  have size : (destination.set 0#usize ids[0]!).length = destination.length := by
    simp [Slice.set, Slice.setAtNat, Slice.length]
  rw [write_at _ 1#usize _ (by change 1 < (destination.set 0#usize ids[0]!).length; omega)]
  congr 1
  apply Slice.ext
  obtain ⟨a, b, input⟩ := two_list ids.val two
  obtain ⟨a', b', output⟩ := two_list destination.val (room.trans two)
  simp [Slice.set_val_eq, Slice.getElem!_Nat_eq, input, output]

#print axioms write_status_refines
#print axioms window_check

end BulksketchBridge.PublicationWrite
