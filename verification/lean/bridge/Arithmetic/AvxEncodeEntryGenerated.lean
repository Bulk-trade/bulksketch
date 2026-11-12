-- Checked original AVX encoder and three emitted singleton loop bodies.
import Arithmetic.AvxInsertDispatchGenerated
import Arithmetic.PortableEncodingGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (encode18Model : AvxInsertDispatchRuntime.Batch)
variable (insertModel : {F : Type} → field.BinaryField F → AvxInsertDispatchRuntime.Batch)

local notation "backend.x86_vpclmul512.encode_18" => encode18Model
local notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero" => insertModel

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::encode_nonzero]: loop body 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 152:12-154:13 -/
@[rust_loop_body]
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop0.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.Iter Std.U64) (odd : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U64) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done odd)
  | some id =>
    let s ← core.slice.raw.from_ref id
    let odd1 ←
      backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
        fieldBinaryFieldInst odd s
    ok (cont (iter1, odd1))

local notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop0.body" => (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop0.body insertModel)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::encode_nonzero]: loop 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 152:12-154:13 -/
@[rust_loop]
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop0
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.Iter Std.U64) (odd : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, odd1) =>
      backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop0.body
      fieldBinaryFieldInst iter1 odd1)
    (iter, odd)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::encode_nonzero]: loop body 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 152:12-154:13 -/
@[rust_loop_body]
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop1.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.Iter Std.U64) (odd : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U64) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done odd)
  | some id =>
    let s ← core.slice.raw.from_ref id
    let odd1 ←
      backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
        fieldBinaryFieldInst odd s
    ok (cont (iter1, odd1))

local notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop1.body" => (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop1.body insertModel)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::encode_nonzero]: loop 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 152:12-154:13 -/
@[rust_loop]
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop1
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.Iter Std.U64) (odd : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, odd1) =>
      backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop1.body
      fieldBinaryFieldInst iter1 odd1)
    (iter, odd)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::encode_nonzero]: loop body 2:
    Source: 'src/backend/x86_vpclmul512.rs', lines 152:12-154:13 -/
@[rust_loop_body]
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop2.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.Iter Std.U64) (odd : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U64) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done odd)
  | some id =>
    let s ← core.slice.raw.from_ref id
    let odd1 ←
      backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
        fieldBinaryFieldInst odd s
    ok (cont (iter1, odd1))

local notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop2.body" => (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop2.body insertModel)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::encode_nonzero]: loop 2:
    Source: 'src/backend/x86_vpclmul512.rs', lines 152:12-154:13 -/
@[rust_loop]
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop2
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.Iter Std.U64) (odd : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, odd1) =>
      backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop2.body
      fieldBinaryFieldInst iter1 odd1)
    (iter, odd)

local notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop0" => (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop0 insertModel)
local notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop1" => (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop1 insertModel)
local notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop2" => (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop2 insertModel)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::encode_nonzero]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 144:4-158:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (odd : Slice Std.U64) (ids : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let i ← fieldBinaryFieldInst.BITS
  if i = 64#u32
  then
    let i1 := Slice.len odd
    if i1 = 18#usize
    then
      let i2 := Slice.len ids
      let b ← match i2.val with
                | 1 => ok true
                | 2 => ok true
                | _ => ok false
      if b
      then backend.x86_vpclmul512.encode_18 odd ids
      else
        let odd1 ← core.slice.Slice.fill core.clone.CloneU64 odd 0#u64
        let i3 := Slice.len ids
        if i3 <= 2#usize
        then
          let iter ←
            SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
              ids
          backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop0
            fieldBinaryFieldInst iter odd1
        else
          backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
            fieldBinaryFieldInst odd1 ids
    else
      let odd1 ← core.slice.Slice.fill core.clone.CloneU64 odd 0#u64
      let i2 := Slice.len ids
      if i2 <= 2#usize
      then
        let iter ←
          SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
            ids
        backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop1
          fieldBinaryFieldInst iter odd1
      else
        backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
          fieldBinaryFieldInst odd1 ids
  else
    let odd1 ← core.slice.Slice.fill core.clone.CloneU64 odd 0#u64
    let i1 := Slice.len ids
    if i1 <= 2#usize
    then
      let iter ←
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
          ids
      backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.encode_nonzero_loop2
        fieldBinaryFieldInst iter odd1
    else
      backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
        fieldBinaryFieldInst odd1 ids

end bulksketch
