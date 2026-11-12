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

/-- [bulksketch::decode::deg34::normalize]: loop body 0:
    Source: 'src/decode/deg34.rs', lines 72:4-74:5 -/
@[rust_loop_body]
def decode.deg34.normalize_loop.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (cleared : Slice Std.U64) (inverse : Std.U64)
  (iter : core.ops.range.Range Std.Usize) (factor : Slice Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done factor)
  | some index =>
    let i ← Slice.index_usize cleared index
    let i1 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i inverse
    let s ← Slice.update factor index i1
    ok (cont (iter1, s))

/-- [bulksketch::decode::deg34::normalize]: loop 0:
    Source: 'src/decode/deg34.rs', lines 72:4-74:5 -/
@[rust_loop]
def decode.deg34.normalize_loop
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.Usize) (cleared : Slice Std.U64)
  (factor : Slice Std.U64) (inverse : Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, factor1) => decode.deg34.normalize_loop.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst cleared inverse iter1
      factor1)
    (iter, factor)

/-- [bulksketch::decode::deg34::normalize]:
    Source: 'src/decode/deg34.rs', lines 65:0-77:1 -/
def decode.deg34.normalize
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (cleared : Slice Std.U64) (s : Std.U64) (degree : Std.Usize)
  (factor : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let i ← Slice.index_usize cleared 5#usize
  let o ← backendcontractBulkKernelsInst.ArithmeticInst.inverse i
  let inverse ←
    core.option.Option.expect o (toStr "passed nonsingular Newton guard")
  let i1 ← degree - 1#usize
  let factor1 ←
    decode.deg34.normalize_loop fieldBinaryFieldInst
      backendcontractBulkKernelsInst { start := 0#usize, «end» := i1 }
      cleared factor inverse
  let i2 ← degree - 1#usize
  let factor2 ← Slice.update factor1 i2 s
  Slice.update factor2 degree 1#u64

end bulksketch
