-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.SliceKernelTypes
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::types::{impl core::default::Default for bulksketch::types::RawProduct}::default]:
    Source: 'src/types.rs', lines 266:29-266:36
    Visibility: public -/
def types.RawProduct.Insts.CoreDefaultDefault.default
  : Result types.RawProduct := do
  ok
    {
      lo := (core.default.DefaultU64.default),
      hi := (core.default.DefaultU64.default)
    }

/-- [bulksketch::backend::contract::BulkKernels::odd_recurrence_matches]: loop body 1:
    Source: 'src/backend/contract.rs', lines 72:12-76:13 -/
@[rust_loop_body, trait_default]
def
  backend.contract.BulkKernels.odd_recurrence_matches.default_loop0_loop0.body
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (odd : Slice Std.U64) (squared_locator : Slice Std.U64)
  (index : Std.Usize) (iter : core.ops.range.RangeInclusive Std.Usize)
  (sum : types.RawProduct) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) ×
    types.RawProduct) types.RawProduct)
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done sum)
  | some lag =>
    let i ← index - lag
    let i1 ← Slice.index_usize odd i
    let i2 ← Slice.index_usize squared_locator lag
    let product ← BulkKernelsInst.ArithmeticInst.raw_mul i1 i2
    let i3 ← lift (sum.lo ^^^ product.lo)
    let i4 ← lift (sum.hi ^^^ product.hi)
    ok (cont (iter1, { lo := i3, hi := i4 }))

/-- [bulksketch::backend::contract::BulkKernels::odd_recurrence_matches]: loop 1:
    Source: 'src/backend/contract.rs', lines 72:12-76:13 -/
@[rust_loop, trait_default]
def backend.contract.BulkKernels.odd_recurrence_matches.default_loop0_loop0
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (iter : core.ops.range.RangeInclusive Std.Usize)
  (odd : Slice Std.U64) (squared_locator : Slice Std.U64) (index : Std.Usize)
  (sum : types.RawProduct) :
  Result types.RawProduct
  := do
  loop
    (fun (iter1, sum1) =>
      backend.contract.BulkKernels.odd_recurrence_matches.default_loop0_loop0.body
      BulkKernelsInst odd squared_locator index iter1 sum1)
    (iter, sum)

/-- [bulksketch::backend::contract::BulkKernels::odd_recurrence_matches]: loop body 0:
    Source: 'src/backend/contract.rs', lines 70:8-82:5 -/
@[rust_loop_body, trait_default]
def backend.contract.BulkKernels.odd_recurrence_matches.default_loop0.body
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (odd : Slice Std.U64) (squared_locator : Slice Std.U64)
  (degree : Std.Usize) (iter : core.ops.range.Range Std.Usize) :
  Result (ControlFlow (core.ops.range.Range Std.Usize) Bool)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done true)
  | some index =>
    let sum ← types.RawProduct.Insts.CoreDefaultDefault.default
    let iter2 ← core.ops.range.RangeInclusive.new 1#usize degree
    let sum1 ←
      backend.contract.BulkKernels.odd_recurrence_matches.default_loop0_loop0
        BulkKernelsInst iter2 odd squared_locator index sum
    let i ← BulkKernelsInst.ArithmeticInst.reduce sum1
    let i1 ← Slice.index_usize odd index
    if i != i1
    then ok (done false)
    else ok (cont iter1)

/-- [bulksketch::backend::contract::BulkKernels::odd_recurrence_matches]: loop 0:
    Source: 'src/backend/contract.rs', lines 70:8-82:5 -/
@[rust_loop, trait_default]
def backend.contract.BulkKernels.odd_recurrence_matches.default_loop0
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (iter : core.ops.range.Range Std.Usize) (odd : Slice Std.U64)
  (squared_locator : Slice Std.U64) (degree : Std.Usize) :
  Result Bool
  := do
  loop
    (fun iter1 =>
      backend.contract.BulkKernels.odd_recurrence_matches.default_loop0.body
      BulkKernelsInst odd squared_locator degree iter1)
    iter

/-- [bulksketch::backend::contract::BulkKernels::odd_recurrence_matches]:
    Source: 'src/backend/contract.rs', lines 68:4-82:5 -/
@[trait_default]
def backend.contract.BulkKernels.odd_recurrence_matches.default
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (odd : Slice Std.U64) (squared_locator : Slice Std.U64) :
  Result Bool
  := do
  let i := Slice.len squared_locator
  let degree ← i - 1#usize
  let i1 := Slice.len odd
  backend.contract.BulkKernels.odd_recurrence_matches.default_loop0
    BulkKernelsInst { start := degree, «end» := i1 } odd squared_locator
    degree

end bulksketch
