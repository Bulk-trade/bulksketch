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

/-- [bulksketch::backend::contract::BulkKernels::square_mod]:
    Source: 'src/backend/contract.rs', lines 53:4-55:5 -/
@[trait_default]
def backend.contract.BulkKernels.square_mod.default
  (Self : Type _) (F : Type _) (_a : Slice Std.U64) (_table : Slice Std.U64)
  (_dst : Slice Std.U64) (_raw : Slice types.RawProduct) :
  Result (Bool × (Slice Std.U64) × (Slice types.RawProduct))
  := do
  ok (false, _dst, _raw)

/-- [bulksketch::backend::contract::BulkKernels::multiply_linear]: loop body 0:
    Source: 'src/backend/contract.rs', lines 60:8-62:9 -/
@[rust_loop_body, trait_default]
def backend.contract.BulkKernels.multiply_linear.default_loop.body
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (root : Std.U64)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (coefficients : Slice Std.U64) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × (Slice Std.U64)) (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done coefficients)
  | some index =>
    let i ← index - 1#usize
    let i1 ← Slice.index_usize coefficients i
    let i2 ← BulkKernelsInst.ArithmeticInst.mul i1 root
    let i3 ← Slice.index_usize coefficients index
    let i4 ← lift (i3 ^^^ i2)
    let s ← Slice.update coefficients index i4
    ok (cont (iter1, s))

/-- [bulksketch::backend::contract::BulkKernels::multiply_linear]: loop 0:
    Source: 'src/backend/contract.rs', lines 60:8-62:9 -/
@[rust_loop, trait_default]
def backend.contract.BulkKernels.multiply_linear.default_loop
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (coefficients : Slice Std.U64) (root : Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, coefficients1) =>
      backend.contract.BulkKernels.multiply_linear.default_loop.body
      BulkKernelsInst root iter1 coefficients1)
    (iter, coefficients)

/-- [bulksketch::backend::contract::BulkKernels::multiply_linear]:
    Source: 'src/backend/contract.rs', lines 59:4-63:5 -/
@[trait_default]
def backend.contract.BulkKernels.multiply_linear.default
  {Self : Type _} {F : Type _} (BulkKernelsInst : backend.contract.BulkKernels
  Self F) (coefficients : Slice Std.U64) (root : Std.U64) :
  Result (Slice Std.U64)
  := do
  let i := Slice.len coefficients
  let iter ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) { start := 1#usize, «end» := i }
  backend.contract.BulkKernels.multiply_linear.default_loop BulkKernelsInst
    iter coefficients root

end bulksketch
