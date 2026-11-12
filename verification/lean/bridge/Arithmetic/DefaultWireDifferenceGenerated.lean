-- Exact original BulkKernels difference with scoped nested Zip bindings.
import Arithmetic.DefaultWireDifferenceRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

local notation "core.iter.traits.iterator.Iterator.zip.trait_default" =>
  BulksketchBridge.DefaultWireDifferenceRuntime.zip
local notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair" =>
  BulksketchBridge.DefaultWireDifferenceRuntime.innerDictionary
local notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next" =>
  BulksketchBridge.DefaultWireDifferenceRuntime.next

/-- [bulksketch::backend::contract::BulkKernels::difference]: loop body 0:
    Source: 'src/backend/contract.rs', lines 113:8-116:9 -/
@[rust_loop_body, trait_default]
def backend.contract.BulkKernels.difference.default_loop.body
  (iter : core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
  (core.slice.iter.ChunksExact Std.U8))
  (back : core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
  (core.slice.iter.ChunksExact Std.U8) → core.iter.adapters.zip.Zip
  (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64)) (core.slice.iter.ChunksExact Std.U8))
  (any : Std.U64) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
    (core.slice.iter.ChunksExact Std.U8)) × (core.iter.adapters.zip.Zip
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)) (core.slice.iter.ChunksExact Std.U8) →
    core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
    (core.slice.iter.ChunksExact Std.U8)) × Std.U64) (Std.U64 ×
    (core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
    (core.slice.iter.ChunksExact Std.U8))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64))
      (core.iter.traits.iterator.IteratorChunksExact Std.U8) iter
  match o with
  | none => ok (done (any, let z := next_back iter1 none
                           back z))
  | some p =>
    let ((_, word), bytes) := p
    let r ←
      core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8
        bytes
    let a ←
      core.result.Result.expect core.fmt.DebugTryFromSliceError r (toStr
        "complete word")
    let i ← lift (core.num.U64.from_le_bytes a)
    let out ← lift (word ^^^ i)
    let any1 ← lift (any ||| out)
    ok (cont (iter1,
      fun z => let z1 := next_back z (some ((out, word), bytes))
               back z1, any1))

/-- [bulksketch::backend::contract::BulkKernels::difference]: loop 0:
    Source: 'src/backend/contract.rs', lines 113:8-116:9 -/
@[rust_loop, trait_default]
def backend.contract.BulkKernels.difference.default_loop
  (iter : core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
  (core.slice.iter.ChunksExact Std.U8))
  (back : core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
  (core.slice.iter.ChunksExact Std.U8) → core.iter.adapters.zip.Zip
  (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64)) (core.slice.iter.ChunksExact Std.U8))
  (any : Std.U64) :
  Result (Std.U64 × (core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
    (core.slice.iter.ChunksExact Std.U8)))
  := do
  loop
    (fun (iter1, back1, any1) =>
      backend.contract.BulkKernels.difference.default_loop.body iter1 back1
      any1)
    (iter, back, any)

/-- [bulksketch::backend::contract::BulkKernels::difference]:
    Source: 'src/backend/contract.rs', lines 103:4-118:5 -/
@[trait_default]
def backend.contract.BulkKernels.difference.default
  (Self : Type _) (F : Type _) (dst : Slice Std.U64)
  («local» : Slice Std.U64) (remote : Slice Std.U8) :
  Result (Bool × (Slice Std.U64))
  := do
  let left_val := Slice.len dst
  let right_val := Slice.len «local»
  if left_val = right_val
  then
    let left_val1 := Slice.len remote
    let i := Slice.len dst
    let right_val1 ← 8#usize * i
    if left_val1 = right_val1
    then
      let (im, iter_mut_back) ← core.slice.Slice.iter_mut dst
      let (z, trait_default_back) ←
        core.iter.traits.iterator.Iterator.zip.trait_default
          (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
          Std.U64)
          (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
          Std.U64) im «local»
      let ce ← core.slice.Slice.chunks_exact remote 8#usize
      let (iter, trait_default_back1) ←
        core.iter.traits.iterator.Iterator.zip.trait_default
          (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
          (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
          Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64))
          (core.iter.traits.collect.IntoIterator.Blanket
          (core.iter.traits.iterator.IteratorChunksExact Std.U8)) z ce
      let (any, back) ←
        backend.contract.BulkKernels.difference.default_loop iter
          (fun z1 => z1) 0#u64
      let z1 := trait_default_back1 back
      let im1 := trait_default_back z1
      let dst1 := iter_mut_back im1
      ok (any != 0#u64, dst1)
    else
      let _ ←
        core.fmt.Arguments.from_str (toStr "difference byte length mismatch")
      fail panic
  else
    let _ ← core.fmt.Arguments.from_str (toStr "difference length mismatch")
    fail panic

end bulksketch
