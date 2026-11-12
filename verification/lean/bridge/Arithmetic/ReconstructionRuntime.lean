module
public import Aeneas
@[expose] public section

namespace Aeneas.Std.ReconstructionRuntime

/-- The callback is consumed by `Iterator::all`. The result records the
number of elements consumed, including the first false callback. -/
def scan {T C : Type} (call : C → T → Result (Bool × C)) :
    List T → C → Result (Bool × Nat)
  | [], _ => .ok (true, 0)
  | value :: remaining, closure => do
    let (passed, closure) ← call closure value
    if passed then
      let (allPassed, count) ← scan call remaining closure
      .ok (allPassed, count + 1)
    else
      .ok (false, 1)

/-- The pinned slice iterator tracks the original slice and current offset.
This binding preserves short circuiting, closure sequencing and the exact
remaining offset of the consuming slice iterator. -/
def sliceAll {T C : Type} (dictionary : core.ops.function.FnMut C T Bool)
    (iter : core.slice.iter.Iter T) (closure : C) :
    Result (Bool × core.slice.iter.Iter T) := do
  let (allPassed, count) ← scan dictionary.call_mut (iter.slice.val.drop iter.i) closure
  .ok (allPassed, {iter with i := iter.i + count})

end Aeneas.Std.ReconstructionRuntime
