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

/-- [bulksketch::decode::affine::linear_eval]: loop body 0:
    Source: 'src/decode/affine.rs', lines 236:4-241:5 -/
@[rust_loop_body]
def decode.affine.linear_eval_loop.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (linear : Slice Std.U64)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (x : Std.U64) (out : Std.U64) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × Std.U64 × Std.U64) Std.U64)
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done out)
  | some p =>
    let (i, coefficient) := p
    let i1 ← backendcontractBulkKernelsInst.ArithmeticInst.mul coefficient x
    let out1 ← lift (out ^^^ i1)
    let i2 ← i + 1#usize
    let i3 := Slice.len linear
    if i2 != i3
    then
      let x1 ← backendcontractBulkKernelsInst.ArithmeticInst.square x
      ok (cont (iter1, x1, out1))
    else ok (cont (iter1, x, out1))

/-- [bulksketch::decode::affine::linear_eval]: loop 0:
    Source: 'src/decode/affine.rs', lines 236:4-241:5 -/
@[rust_loop]
def decode.affine.linear_eval_loop
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (linear : Slice Std.U64) (x : Std.U64) (out : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (iter1, x1, out1) => decode.affine.linear_eval_loop.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst linear iter1 x1 out1)
    (iter, x, out)

/-- [bulksketch::decode::affine::linear_eval]:
    Source: 'src/decode/affine.rs', lines 234:0-243:1 -/
def decode.affine.linear_eval
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (linear : Slice Std.U64) (x : Std.U64) :
  Result Std.U64
  := do
  let i ← core.slice.Slice.iter linear
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) i
  decode.affine.linear_eval_loop fieldBinaryFieldInst
    backendcontractBulkKernelsInst iter linear x 0#u64

end bulksketch
