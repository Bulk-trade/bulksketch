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

/-- [bulksketch::backend::contract::BulkKernels::encode_nonzero]: loop body 0:
    Source: 'src/backend/contract.rs', lines 91:12-93:13 -/
@[rust_loop_body, trait_default]
def backend.contract.BulkKernels.encode_nonzero.default_loop.body
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (iter : core.slice.iter.Iter Std.U64) (odd : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U64) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done odd)
  | some id =>
    let s ← core.slice.raw.from_ref id
    let odd1 ← BulkKernelsInst.insert_nonzero odd s
    ok (cont (iter1, odd1))

/-- [bulksketch::backend::contract::BulkKernels::encode_nonzero]: loop 0:
    Source: 'src/backend/contract.rs', lines 91:12-93:13 -/
@[rust_loop, trait_default]
def backend.contract.BulkKernels.encode_nonzero.default_loop
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (iter : core.slice.iter.Iter Std.U64) (odd : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, odd1) =>
      backend.contract.BulkKernels.encode_nonzero.default_loop.body
      BulkKernelsInst iter1 odd1)
    (iter, odd)

/-- [bulksketch::backend::contract::BulkKernels::encode_nonzero]:
    Source: 'src/backend/contract.rs', lines 88:4-97:5 -/
@[trait_default]
def backend.contract.BulkKernels.encode_nonzero.default
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (odd : Slice Std.U64) (ids : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let odd1 ← core.slice.Slice.fill core.clone.CloneU64 odd 0#u64
  let i := Slice.len ids
  if i <= 2#usize
  then
    let iter ←
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
        ids
    backend.contract.BulkKernels.encode_nonzero.default_loop BulkKernelsInst
      iter odd1
  else BulkKernelsInst.insert_nonzero odd1 ids

end bulksketch
