module
public import Aeneas
@[expose] public section

namespace Aeneas.Std.PortableHornerRuntime

/-- Value model of a shared slice split, preserving its order and element type. -/
def splitLast {T : Type} (slice : Slice T) : Result (Option (T × Slice T)) :=
  .ok (slice.val.getLast?.map fun last =>
    (last, Slice.from slice.val.dropLast (by
      rw [List.length_dropLast]
      exact (Nat.sub_le _ _).trans slice.length_ineq)))

/-- The reverse fold calls the actual backwards iterator step and threads the
mutable callback state through every call. This models the shared slice
specialization used by the extraction. -/
def foldBody {I Acc F T : Type}
    (iterator : core.iter.traits.double_ended.DoubleEndedIterator I T)
    (callback : core.ops.function.FnMut F (Acc × T) Acc)
    (state : I × Acc × F) : Result (ControlFlow (I × Acc × F) Acc) := do
  let (item, next) ← iterator.next_back state.1
  match item with
  | none => .ok (.done state.2.1)
  | some value =>
    let (accumulator, function) ← callback.call_mut state.2.2 (state.2.1, value)
    .ok (.cont (next, accumulator, function))

def reverseFold {I Acc F T : Type}
    (iterator : core.iter.traits.double_ended.DoubleEndedIterator I T)
    (callback : core.ops.function.FnMut F (Acc × T) Acc)
    (reverse : core.iter.adapters.rev.Rev I) (initial : Acc) (function : F) :
    Result Acc :=
  loop (foldBody iterator callback) (reverse.iter, initial, function)

end Aeneas.Std.PortableHornerRuntime
