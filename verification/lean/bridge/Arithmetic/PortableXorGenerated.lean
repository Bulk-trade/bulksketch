-- Exact original XOR declarations. Only imports and scoped std bindings are adapted.
module
public import Arithmetic.Types
public import Arithmetic.MutableZipRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::xor_assign]: loop body 0:
    Source: 'src/backend/portable.rs', lines 104:8-106:9 -/
@[rust_loop_body]
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.xor_assign_loop.body
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    Std.U64) (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))) (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (let z := next_back iter1 none
                      back z))
  | some p =>
    let (target, source) := p
    let target1 ← lift (target ^^^ source)
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (target1, source))
               back z1))

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::xor_assign]: loop 0:
    Source: 'src/backend/portable.rs', lines 104:8-106:9 -/
@[rust_loop]
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.xor_assign_loop
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))
  := do
  loop
    (fun (iter1, back1) =>
      backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.xor_assign_loop.body
      iter1 back1)
    (iter, back)

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::xor_assign]:
    Source: 'src/backend/portable.rs', lines 102:4-107:5 -/
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.xor_assign
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (dst : Slice Std.U64) (src : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let left_val := Slice.len dst
  let right_val := Slice.len src
  if left_val = right_val
  then
    let (im, iter_mut_back) ← core.slice.Slice.iter_mut dst
    let (iter, trait_default_back) ←
      core.iter.traits.iterator.Iterator.zip.trait_default
        (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
        Std.U64) (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
        Std.U64) im src
    let back ←
      backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.xor_assign_loop
        iter (fun z => z)
    let im1 := trait_default_back back
    ok (iter_mut_back im1)
  else
    let _ ← core.fmt.Arguments.from_str (toStr "xor_assign length mismatch")
    fail panic

end bulksketch
