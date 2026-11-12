module
public import Arithmetic.MutableZipRuntime
@[expose] public section

namespace Aeneas.Std.DenseSquareRuntime

open Aeneas Aeneas.Std Result

abbrev StepState (T : Type) := core.iter.adapters.step_by.StepBy (core.slice.iter.IterMut T)
abbrev State (T U : Type) := core.iter.adapters.zip.Zip (StepState T) (core.slice.iter.Iter U)

/-- Evidence that the selected mutable component is the pinned slice iterator. -/
structure SliceNext (T : Type) where
  call : MutableZip.LeftNext T
  actual : call = @core.slice.iter.IteratorIterMut.next T

def leftNext (T : Type) : SliceNext T := ⟨core.slice.iter.IteratorIterMut.next, rfl⟩

abbrev StepNext (T : Type) := StepState T →
  Result (Option T × StepState T × (StepState T → Option T → StepState T))

def stepBy {T : Type} (_ : SliceNext T) (iterator : core.slice.iter.IterMut T) (stride : Usize) :
    Result (StepState T × (StepState T → core.slice.iter.IterMut T)) :=
  if stride.val = 0 then fail .panic
  else ok (⟨iterator, stride⟩, fun state => state.iter)

/-- `iter.i` represents the next index to yield. Moving past skipped elements
here is equivalent to `StepBy`'s delayed `nth` on the next call for a slice
iterator. It records a cursor only and writes through the backward operation
for the yielded element, never through any skipped elements. -/
def stepNext {T : Type} (left : SliceNext T) : StepNext T := fun state => do
  let (item, advanced, restore) ← left.call state.iter
  match item with
  | none => ok (none, { state with iter := advanced },
      fun later _ => { later with iter := restore later.iter none })
  | some item =>
    let next := { advanced with i := min advanced.slice.length (state.iter.i + state.step_by.val) }
    ok (some item, { state with iter := next },
      fun later replacement => { later with iter := restore later.iter replacement })

def zip {T U Input : Type} (_ : StepNext T)
    (right : core.iter.traits.collect.IntoIterator Input U (core.slice.iter.Iter U))
    (left : StepState T) (input : Input) : Result (State T U × (State T U → StepState T)) := do
  let iterator ← right.into_iter input
  ok (⟨left, iterator⟩, fun state => state.fst)

/-- `StepBy<IterMut<T>>` uses the ordinary `Zip` front traversal. The right
iterator advances only after a left yield. A missing right item retains the
left cursor advance and releases that borrow without a write. -/
def next {T U : Type} (left : StepNext T)
    (right : core.iter.traits.iterator.Iterator (core.slice.iter.Iter U) U)
    (state : State T U) :
    Result (Option (T × U) × State T U × (State T U → Option (T × U) → State T U)) := do
  let (leftItem, nextLeft, restoreLeft) ← left state.fst
  match leftItem with
  | none => ok (none, ⟨nextLeft, state.snd⟩,
      fun later _ => ⟨restoreLeft later.fst none, later.snd⟩)
  | some leftValue => do
    let (rightItem, nextRight) ← right.next state.snd
    ok (rightItem.map (fun value => (leftValue, value)), ⟨nextLeft, nextRight⟩,
      fun later replacement =>
        ⟨restoreLeft later.fst (rightItem.bind fun _ => replacement.map Prod.fst), later.snd⟩)

end Aeneas.Std.DenseSquareRuntime
