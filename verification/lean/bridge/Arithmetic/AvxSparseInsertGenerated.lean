-- Original checked sparse insertion with its recursive insert callee bound explicitly.
import Arithmetic.AvxInsertDispatchGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

variable (insertModel : AvxInsertDispatchRuntime.Batch)
local notation "backend.x86_vpclmul512.insert" => insertModel

/-- [bulksketch::backend::x86_vpclmul512::insert_sparse]: loop body 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 432:4-434:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.insert_sparse_loop.body
  (iter : core.slice.iter.Iter Std.U64) (odd : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U64) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done odd)
  | some id =>
    let s ← lift (Array.to_slice (Array.make 1#usize [ id ]))
    let odd1 ← backend.x86_vpclmul512.insert odd s
    ok (cont (iter1, odd1))

local notation "backend.x86_vpclmul512.insert_sparse_loop.body" => (backend.x86_vpclmul512.insert_sparse_loop.body insertModel)

/-- [bulksketch::backend::x86_vpclmul512::insert_sparse]: loop 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 432:4-434:5 -/
@[rust_loop]
def backend.x86_vpclmul512.insert_sparse_loop
  (iter : core.slice.iter.Iter Std.U64) (odd : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, odd1) => backend.x86_vpclmul512.insert_sparse_loop.body iter1
      odd1)
    (iter, odd)

local notation "backend.x86_vpclmul512.insert_sparse_loop" => (backend.x86_vpclmul512.insert_sparse_loop insertModel)

/-- [bulksketch::backend::x86_vpclmul512::insert_sparse]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 431:0-435:1 -/
def backend.x86_vpclmul512.insert_sparse
  (odd : Slice Std.U64) (ids : Slice Std.U64) : Result (Slice Std.U64) := do
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter ids
  backend.x86_vpclmul512.insert_sparse_loop iter odd

end bulksketch
