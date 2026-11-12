-- Exact original declarations. Only imports and scoped std bindings are adapted.
module
public import Arithmetic.PortableEncodingRuntime
public import Arithmetic.PortableGenerated
public import Arithmetic.SliceKernelTypes
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::insert_nonzero]: loop body 1:
    Source: 'src/backend/portable.rs', lines 95:12-98:13 -/
@[rust_loop_body]
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (square : Std.U64)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (power : Std.U64) :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64) ×
    Std.U64) ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut
    Std.U64 → core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some syndrome =>
    let power1 ←
      backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.mul
        fieldBinaryFieldInst power square
    let syndrome1 ← lift (syndrome ^^^ power1)
    ok (cont (iter1,
      fun im => let im1 := next_back im (some syndrome1)
                back im1, power1))

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::insert_nonzero]: loop 1:
    Source: 'src/backend/portable.rs', lines 95:12-98:13 -/
@[rust_loop]
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (square : Std.U64) (power : Std.U64) :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1, power1) =>
      backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0.body
      fieldBinaryFieldInst square iter1 back1 power1)
    (iter, back, power)

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::insert_nonzero]: loop body 0:
    Source: 'src/backend/portable.rs', lines 90:8-99:9 -/
@[rust_loop_body]
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.Iter Std.U64) (first : Std.U64)
  (successors : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U64) × Std.U64 × (Slice
    Std.U64)) (Std.U64 × (Slice Std.U64)))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (first, successors))
  | some id =>
    let first1 ← lift (first ^^^ id)
    let square ←
      backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.square
        fieldBinaryFieldInst id
    let (iter2, into_iter_back) ←
      MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
        successors
    let (im, back) ←
      backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0_loop0
        fieldBinaryFieldInst iter2 (fun im1 => im1) square id
    let im1 := back im
    let s := into_iter_back im1
    ok (cont (iter1, first1, s))

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::insert_nonzero]: loop 0:
    Source: 'src/backend/portable.rs', lines 90:8-99:9 -/
@[rust_loop]
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.Iter Std.U64) (first : Std.U64)
  (successors : Slice Std.U64) :
  Result (Std.U64 × (Slice Std.U64))
  := do
  loop
    (fun (iter1, first1, successors1) =>
      backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0.body
      fieldBinaryFieldInst iter1 first1 successors1)
    (iter, first, successors)

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::insert_nonzero]:
    Source: 'src/backend/portable.rs', lines 85:4-100:5 -/
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (odd : Slice Std.U64) (ids : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let (o, split_first_mut_back) ← core.slice.Slice.split_first_mut odd
  match o with
  | none => ok (split_first_mut_back none)
  | some p =>
    let (first, successors) := p
    let iter ←
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
        ids
    let (first1, successors1) ←
      backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero_loop0
        fieldBinaryFieldInst iter first successors
    ok (split_first_mut_back (some (first1, successors1)))

end bulksketch
