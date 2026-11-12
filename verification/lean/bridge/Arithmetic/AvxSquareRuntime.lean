import Arithmetic.Avx512RegisterGenerated
import Arithmetic.DenseReducerSquareRuntime
import Arithmetic.X86PclmulGenerated

namespace Aeneas.Std.AvxSquareRuntime

open Avx512Register

abbrev Load := Slice U64 → Result Word512
abbrev Store := Slice U64 → Word512 → Result (Slice U64)

def zero : Result Word512 := .ok (fun _ _ => 0)

structure Skip (I : Type) where
  iter : I
  count : Usize

/-- Rust Skip delays dropping the initial count until the first next. -/
def skip {I Item : Type} (_ : core.iter.traits.iterator.Iterator I Item)
    (iter : I) (count : Usize) : Result (Skip I) :=
  .ok ⟨iter, count⟩

/-- Read-only finite iterators have no effects beyond the cursor, so
discarding the requested prefix by repeated next calls is exact. -/
def skipNext {I Item : Type} (inst : core.iter.traits.iterator.Iterator I Item)
    (state : Skip I) : Result (Option Item × Skip I) := do
  let iter ← core.iter.adapters.step_by.skipN inst state.iter state.count.val
  let (item, next) ← inst.next iter
  .ok (item, ⟨next, 0#usize⟩)

end Aeneas.Std.AvxSquareRuntime
