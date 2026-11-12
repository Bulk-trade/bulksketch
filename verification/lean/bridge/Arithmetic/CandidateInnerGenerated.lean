-- Exact original checked candidate Zip loop declarations.
import Arithmetic.MutableZipRuntime

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

local notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next" =>
  Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::candidates]: loop body 1:
    Source: 'src/decode/stages.rs', lines 291:12-303:5 -/
@[rust_loop_body]
def decode.stages.Execution.candidates_loop0_loop0.body
  (i : Std.Usize) (return_from_inner : Bool)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U64)
  (core.slice.iter.Iter Std.U64)) (i1 : Std.Usize) (s : Slice Std.U64) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.Iter
    Std.U64) (core.slice.iter.Iter Std.U64)) × Std.Usize × (Slice Std.U64))
    (Std.Usize × (Slice Std.U64) × Bool))
  := do
  let (o, iter1) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64)
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (i1, s, return_from_inner))
  | some p =>
    let (point, value) := p
    if value = 0#u64
    then
      if i1 = i
      then ok (done (i1, s, true))
      else
        let s1 ← Slice.update s i1 point
        let i2 ← i1 + 1#usize
        ok (cont (iter1, i2, s1))
    else ok (cont (iter1, i1, s))

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::candidates]: loop 1:
    Source: 'src/decode/stages.rs', lines 291:12-303:5 -/
@[rust_loop]
def decode.stages.Execution.candidates_loop0_loop0
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Iter Std.U64)
  (core.slice.iter.Iter Std.U64)) (i : Std.Usize) (i1 : Std.Usize)
  (s : Slice Std.U64) (return_from_inner : Bool) :
  Result (Std.Usize × (Slice Std.U64) × Bool)
  := do
  loop
    (fun (iter1, i2, s1) => decode.stages.Execution.candidates_loop0_loop0.body
      i return_from_inner iter1 i2 s1)
    (iter, i1, s)

end bulksketch
