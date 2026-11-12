module
public import Arithmetic.ShapeWireRuntime
@[expose] public section

/-! Value model of the pinned shared slice iterator specialization of `any`.
Each predicate call threads its FnMut state. A match consumes its element
and returns before observing any later element. -/
namespace Aeneas.Std.DirectTwoRuntime

def scan {T F : Type} (call : core.ops.function.FnMut F T Bool) :
    Nat → core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T)
  | 0, iterator, _ => Result.ok (false, iterator)
  | fuel + 1, iterator, callback => do
    let (item, advanced) ← core.slice.iter.IteratorSliceIter.next iterator
    match item with
    | none => Result.ok (false, advanced)
    | some value =>
      let (found, callback') ← call.call_mut callback value
      if found then Result.ok (true, advanced)
      else scan call fuel advanced callback'

def sharedAny {T F : Type} (call : core.ops.function.FnMut F T Bool)
    (iterator : core.slice.iter.Iter T) (callback : F) :
    Result (Bool × core.slice.iter.Iter T) :=
  scan call (iterator.slice.length - iterator.i) iterator callback

end Aeneas.Std.DirectTwoRuntime
