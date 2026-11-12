import BulksketchBridge.PortableInsertionLoop
import BulksketchBridge.AvxTileChunkSum

namespace BulksketchBridge.AvxTileDoubleZip

open Aeneas Aeneas.Std Result

abbrev Paired (T U : Type) :=
  core.iter.adapters.zip.Zip (core.slice.iter.IterMut T) (core.slice.iter.IterMut U)

def overwrite {T : Type} (index : Nat) (later : core.slice.iter.IterMut T)
    (replacement : Option T) : core.slice.iter.IterMut T :=
  match replacement with
  | none => later
  | some value => { later with slice := later.slice.setAtNat index value }

/-- Rust's specialized slice Zip shares a relative front index and stops at
the shorter component. Separate absolute cursors permit slice subranges. Both
backward projections use the later iterator state, preserving later writes. -/
def nextBoth {T U : Type} (state : Paired T U) :
    Result (Option (T × U) × Paired T U × (Paired T U → Option (T × U) → Paired T U)) :=
  if state.fst.i < state.fst.slice.length ∧ state.snd.i < state.snd.slice.length then do
    let (left, afterLeft, restoreLeft) ← core.slice.iter.IteratorIterMut.next state.fst
    let (right, afterRight, restoreRight) ← core.slice.iter.IteratorIterMut.next state.snd
    ok (left.bind fun l => right.map fun r => (l, r), ⟨afterLeft, afterRight⟩,
      fun later replacement =>
        ⟨restoreLeft later.fst (replacement.map Prod.fst),
          restoreRight later.snd (replacement.map Prod.snd)⟩)
  else ok (none, state, fun later _ => later)

private theorem mutable_next {T : Type} [Inhabited T] (iterator : core.slice.iter.IterMut T)
    (bounded : iterator.i < iterator.slice.length) :
    core.slice.iter.IteratorIterMut.next iterator =
      .ok (some iterator.slice[iterator.i]!, { iterator with i := iterator.i + 1 }, overwrite iterator.i) := by
  have lengthGuard : iterator.i < iterator.slice.len.val := by simpa using bounded
  have step : core.slice.iter.IteratorIterMut.next iterator =
      .ok (some (iterator.slice[iterator.i]'bounded), { iterator with i := iterator.i + 1 },
        overwrite iterator.i) := by
    unfold core.slice.iter.IteratorIterMut.next
    split
    · dsimp only
      congr 3
    · contradiction
  rw [step, Slice.Inhabited_getElem_eq_getElem! iterator.slice iterator.i bounded]

/-- The exact backward pair writes only the two yielded positions of the
later states. Returning no replacement keeps both later states. -/
theorem next_both_active {T U : Type} [Inhabited T] [Inhabited U] (state : Paired T U)
    (left : state.fst.i < state.fst.slice.length) (right : state.snd.i < state.snd.slice.length) :
    nextBoth state =
      .ok (some (state.fst.slice[state.fst.i]!, state.snd.slice[state.snd.i]!),
        ⟨{ state.fst with i := state.fst.i + 1 }, { state.snd with i := state.snd.i + 1 }⟩,
        fun later replacement => ⟨overwrite state.fst.i later.fst (replacement.map Prod.fst),
          overwrite state.snd.i later.snd (replacement.map Prod.snd)⟩) := by
  rw [nextBoth, ite_eq_left ⟨left, right⟩, mutable_next state.fst left, mutable_next state.snd right]
  simp only [bind_ok]
  rfl

theorem next_both_exhausted {T U : Type} (state : Paired T U)
    (exhausted : state.fst.slice.length ≤ state.fst.i ∨ state.snd.slice.length ≤ state.snd.i) :
    nextBoth state = .ok (none, state, fun later _ => later) := by
  have blocked : ¬ (state.fst.i < state.fst.slice.length ∧ state.snd.i < state.snd.slice.length) := by
    rintro ⟨left, right⟩
    cases exhausted <;> omega
  rw [nextBoth, ite_eq_right blocked]

#print axioms next_both_active
#print axioms next_both_exhausted

end BulksketchBridge.AvxTileDoubleZip
