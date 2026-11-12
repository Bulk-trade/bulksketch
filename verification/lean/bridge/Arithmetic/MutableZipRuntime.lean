module
public import Aeneas
@[expose] public section

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.MutableZip

/-- The two indices are virtual front cursors into the original slices. Rust's
slice `Zip` specialization stores a common relative index and a minimum length.
Keeping each absolute cursor represents the same remaining pairs, including
inputs whose component iterators start at different positions. -/
abbrev State (T U : Type) :=
  core.iter.adapters.zip.Zip (core.slice.iter.IterMut T) (core.slice.iter.Iter U)

abbrev LeftNext (T : Type) :=
  core.slice.iter.IterMut T → Result (Option T × core.slice.iter.IterMut T ×
    (core.slice.iter.IterMut T → Option T → core.slice.iter.IterMut T))

/-- A mutable `Iterator::zip` constructor returns the moved iterator and the
projection that restores it when the paired iterator is consumed. -/
def construct {T U Input : Type}
    (right : core.iter.traits.collect.IntoIterator Input U (core.slice.iter.Iter U))
    (left : core.slice.iter.IterMut T) (input : Input) :
    Result (State T U × (State T U → core.slice.iter.IterMut T)) := do
  let iterator ← right.into_iter input
  ok (⟨left, iterator⟩, fun state => state.fst)

/-- The pinned Rust slice specialization exhausts at the shorter side and
leaves both virtual front cursors fixed on exhaustion. On an active step,
compose the pinned `IterMut` backward operation with the left projection of
the returned pair. The callback receives the later iterator, retaining all
writes made by later steps. The shared right iterator is passed through.

The monadic operations supplied to this binding are the original slice
iterator implementations. Their Result effects propagate through bind. -/
def next {T U : Type} (left : LeftNext T)
    (right : core.iter.traits.iterator.Iterator (core.slice.iter.Iter U) U)
    (state : State T U) :
    Result (Option (T × U) × State T U × (State T U → Option (T × U) → State T U)) :=
  if state.fst.i < state.fst.slice.length ∧ state.snd.i < state.snd.slice.length then do
    let (leftItem, nextLeft, restoreLeft) ← left state.fst
    match leftItem with
    | none => ok (none, ⟨nextLeft, state.snd⟩,
        fun later _ => ⟨restoreLeft later.fst none, later.snd⟩)
    | some leftValue => do
      let (rightItem, nextRight) ← right.next state.snd
      ok (rightItem.map (fun value => (leftValue, value)), ⟨nextLeft, nextRight⟩,
        fun later replacement =>
          ⟨restoreLeft later.fst (rightItem.bind fun _ => replacement.map Prod.fst), later.snd⟩)
  else ok (none, state, fun later _ => later)

end Aeneas.Std.MutableZip

namespace bulksketch

/-! Bind the exact names in the original mutable extraction inside its own
namespace. The pinned shared-only bindings keep their existing signatures. -/

def core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT (T : Type) :
    MutableZip.LeftNext T :=
  Aeneas.Std.core.slice.iter.IteratorIterMut.next

def core.iter.traits.iterator.Iterator.zip.trait_default {T U Input : Type}
    (_left : MutableZip.LeftNext T)
    (right : Aeneas.Std.core.iter.traits.collect.IntoIterator Input U
      (Aeneas.Std.core.slice.iter.Iter U)) :=
  MutableZip.construct (T := T) right

abbrev core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next :=
  @MutableZip.next

end bulksketch
