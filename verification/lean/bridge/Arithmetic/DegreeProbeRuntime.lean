module
public import Aeneas
@[expose] public section

namespace Aeneas.Std.DegreeProbeRuntime

/-- The value-level scope is the original unsigned `OrdU64` comparison. -/
def ordered (left right : U64) : Prop := left.val ≤ right.val

def compareWord (left right : U64) : Bool := decide (left.val ≤ right.val)

/-- Concrete ascending permutation of a mutable U64 slice. -/
def sortedWords (words : Slice U64) : Slice U64 :=
  Slice.from (words.val.mergeSort compareWord) (by
    rw [(List.mergeSort_perm words.val compareWord).length_eq]
    exact words.length_ineq)

def sortUnsigned (words : Slice U64) : Result (Slice U64) := .ok (sortedWords words)

/-- The checked unsigned conversion used when a degree-three/four hit records its count. -/
def usizeToU8 (word : Usize) : Result (core.result.Result U8 core.num.error.TryFromIntError) :=
  core.num.tryFromUScalar .U8 word

/-- Left-to-right fold over the remaining shared slice elements. The
callback consumes and returns its closure state on each element. -/
def foldShared {Item Acc C : Type} (callback : core.ops.function.FnMut C (Acc × Item) Acc)
    (iterator : core.slice.iter.Iter Item) (initial : Acc) (closure : C) : Result Acc := do
  let (result, _) ← (iterator.slice.val.drop iterator.i).foldlM
    (fun (accumulator, state) item => callback.call_mut state (accumulator, item))
    (initial, closure)
  .ok result

end Aeneas.Std.DegreeProbeRuntime
