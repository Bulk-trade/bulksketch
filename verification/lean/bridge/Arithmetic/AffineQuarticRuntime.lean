module
public import Aeneas
@[expose] public section

namespace Aeneas.Std.AffineQuarticRuntime

/-- The shared-reference implementation compares the two referents through
the original Ord dictionary. -/
def sharedCmp {A : Type} (order : core.cmp.Ord A) (left right : A) : Result Ordering :=
  order.cmp left right

/-- The fold step of `Iterator::min`. The existing Ord.min supplies the
selection, including the first-on-ties rule for the native shared order. -/
def minimumStep {I Item : Type} (iterator : core.iter.traits.iterator.Iterator I Item)
    (order : core.cmp.Ord Item) (state : I × Item) :
    Result (ControlFlow (I × Item) Item) := do
  let (item, next) ← iterator.next state.1
  match item with
  | none => .ok (.done state.2)
  | some candidate =>
    let least ← order.min state.2 candidate
    .ok (.cont (next, least))

/-- Scoped value model of `Iterator::min = reduce(Ord::min)`. The first next
call provides the initial accumulator, or returns None on exhaustion. -/
def minimum {I Item : Type} (iterator : core.iter.traits.iterator.Iterator I Item)
    (order : core.cmp.Ord Item) (initial : I) : Result (Option Item) := do
  let (first, rest) ← iterator.next initial
  match first with
  | none => .ok none
  | some first =>
    let least ← loop (minimumStep iterator order) (rest, first)
    .ok (some least)

end Aeneas.Std.AffineQuarticRuntime
