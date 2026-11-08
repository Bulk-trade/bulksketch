-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.SliceKernelTypes
public import Arithmetic.CubeRootRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.bool.Bool.then_some" => CubeRootRuntime.thenSome

/-- [bulksketch::decode::deg34::cube_root]: loop body 0:
    Source: 'src/decode/deg34.rs', lines 88:4-90:5 -/
@[rust_loop_body]
def decode.deg34.cube_root_loop.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (t49 : Std.U64) (iter : core.ops.range.Range Std.I32) (u : Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.I32) × Std.U64) Std.U64)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepI32 iter
  match o with
  | none => ok (done u)
  | some _ =>
    let i ← backendcontractBulkKernelsInst.ArithmeticInst.frobenius u 6#u32
    let u1 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i t49
    ok (cont (iter1, u1))

/-- [bulksketch::decode::deg34::cube_root]: loop 0:
    Source: 'src/decode/deg34.rs', lines 88:4-90:5 -/
@[rust_loop]
def decode.deg34.cube_root_loop
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.I32) (t49 : Std.U64) (u : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun (iter1, u1) => decode.deg34.cube_root_loop.body fieldBinaryFieldInst
      backendcontractBulkKernelsInst t49 iter1 u1)
    (iter, u)

/-- [bulksketch::decode::deg34::cube_root]:
    Source: 'src/decode/deg34.rs', lines 84:0-93:1 -/
def decode.deg34.cube_root
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (t : Std.U64) :
  Result (Option Std.U64)
  := do
  let t16 ← backendcontractBulkKernelsInst.ArithmeticInst.frobenius t 4#u32
  let i ← backendcontractBulkKernelsInst.ArithmeticInst.square t16
  let i1 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i t16
  let t49 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i1 t
  let u ←
    decode.deg34.cube_root_loop fieldBinaryFieldInst
      backendcontractBulkKernelsInst { start := 0#i32, «end» := 10#i32 } t49
      t
  let u1 ← backendcontractBulkKernelsInst.ArithmeticInst.mul u t
  let b ←
    if u1 != 0#u64
    then
      do
      let i2 ← backendcontractBulkKernelsInst.ArithmeticInst.square u1
      let i3 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i2 u1
      ok (i3 = t)
    else ok false
  core.bool.Bool.then_some b u1

end bulksketch
