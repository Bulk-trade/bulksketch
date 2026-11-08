module
public import Aeneas
@[expose] public section

namespace bulksketch

open Aeneas Aeneas.Std

/-- The mutable slice IntoIterator binding exposes the pinned iterator's
backward restoration of its slice. -/
abbrev MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter :=
  @Aeneas.Std.core.slice.Slice.iter_mut

/-- `split_first_mut` returns separate head and tail views. A replacement
restores both within the original frame. An absent replacement leaves the
frame intact. The emitted caller restores a tail of the same length. -/
def core.slice.Slice.split_first_mut {T : Type} (slice : Slice T) :
    Result (Option (T × Slice T) × (Option (T × Slice T) → Slice T)) :=
  match words : slice.val with
  | [] => Result.ok (none, fun _ => slice)
  | head :: tail =>
    Result.ok (some (head, Slice.from tail (by
      have bounded := slice.length_ineq
      rw [words, List.length_cons] at bounded
      omega)), fun replacement => match replacement with
        | none => slice
        | some (head, tail) => (slice.setSlice! 1 tail.val).setAtNat 0 head)

/-- `slice::from_ref` creates a shared one-element view. -/
def core.slice.raw.from_ref {T : Type} (value : T) : Result (Slice T) :=
  Result.ok (Slice.from [value] (by scalar_tac))

end bulksketch
