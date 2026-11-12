import Arithmetic.ReversePositionRuntime

namespace BulksketchBridge.ReversePosition

open Aeneas Aeneas.Std

/-- The rightmost matching index in a reversed list is determined by the
length of the initial run of nonmatching elements. -/
def expected {T : Type} (test : T → Bool) (reversed : List T) : Option Nat :=
  if (reversed.takeWhile (fun item => !test item)).length < reversed.length then
    some (reversed.length - (reversed.takeWhile (fun item => !test item)).length - 1)
  else none

/-- The callback may carry any state. Its normal returned Boolean must agree
with the supplied predicate, and the next call uses its returned state. -/
theorem scan_refines {T P : Type} (callback : core.ops.function.FnMut P T Bool)
    (test : T → Bool) (reversed : List T) (initial : P)
    (normal : ∀ state item, ∃ next, callback.call_mut state item = .ok (test item, next)) :
    Aeneas.Std.ReversePosition.scan callback reversed initial = .ok (expected test reversed) := by
  induction reversed generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    obtain ⟨next, call⟩ := normal initial item
    simp only [Aeneas.Std.ReversePosition.scan, call, bind_ok]
    change (if test item then Result.ok (some rest.length)
      else Aeneas.Std.ReversePosition.scan callback rest next) = _
    cases selected : test item with
    | false =>
      simp only [Bool.false_eq_true, ite_false, ih, expected, List.takeWhile_cons,
        selected, Bool.not_false, ite_true, List.length_cons, Nat.add_lt_add_iff_right,
        Nat.add_sub_add_right]
    | true => simp [expected, selected]

/-- Every successful match is within the suffix that was available on entry. -/
theorem expected_index_bound {T : Type} (test : T → Bool) (reversed : List T)
    (index : Nat) (found : expected test reversed = some index) : index < reversed.length := by
  unfold expected at found
  split at found
  · simp only [Option.some.injEq] at found
    omega
  · contradiction

private theorem usize_index (index : Nat) (bound : index ≤ Usize.max) :
    ∃ word : Usize, UScalar.tryMk .Usize index = .ok word ∧ word.val = index := by
  have fits : UScalar.inBounds .Usize index := by
    simp only [Usize.max, Usize.numBits] at bound
    have positive : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.pow_pos (by decide)
    unfold UScalar.inBounds
    omega
  have spec := UScalar.tryMkOpt_eq .Usize index
  cases normal : UScalar.tryMkOpt .Usize index with
  | none =>
    simp only [normal] at spec
    exact False.elim (spec fits)
  | some word =>
    simp only [normal] at spec
    exact ⟨word, by simp [UScalar.tryMk, normal, Result.ofOption], spec.1⟩

/-- Shared-slice rposition returns a lossless index and the unvisited slice
prefix. The proof applies to an already-advanced iterator as well. -/
theorem shared_rposition_refines {T P : Type} (callback : core.ops.function.FnMut P T Bool)
    (exactSize : core.iter.traits.exact_size.ExactSizeIterator (core.slice.iter.Iter T) T)
    (doubleEnded : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.Iter T) T)
    (iterator : core.slice.iter.Iter T) (predicate : P) (test : T → Bool)
    (normal : ∀ state item, ∃ next, callback.call_mut state item = .ok (test item, next)) :
    ∃ result : Option Usize,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rposition
        callback exactSize doubleEnded iterator predicate =
        .ok (result, Aeneas.Std.ReversePosition.retain iterator
          (iterator.i + (result.map UScalar.val).getD 0)) ∧
      result.map UScalar.val = expected test (iterator.slice.val.drop iterator.i).reverse := by
  have scan := scan_refines callback test (iterator.slice.val.drop iterator.i).reverse predicate normal
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rposition
  simp only [scan, bind_ok]
  cases found : expected test (iterator.slice.val.drop iterator.i).reverse with
  | none => exact ⟨none, rfl, rfl⟩
  | some index =>
    have bound := expected_index_bound test (iterator.slice.val.drop iterator.i).reverse index found
    simp only [List.length_reverse, List.length_drop] at bound
    have fits : index ≤ Usize.max := Nat.le_trans (by omega) iterator.slice.length_ineq
    obtain ⟨word, convert, value⟩ := usize_index index fits
    refine ⟨some word, ?_, ?_⟩
    · simp only [convert, bind_ok, Option.map_some, Option.getD_some, value]
    · simp only [Option.map_some, value]

end BulksketchBridge.ReversePosition
