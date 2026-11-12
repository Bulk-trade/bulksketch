-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.CubeRootGenerated
public import Arithmetic.ShapeWireRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.bool.Bool.then_some" => CubeRootRuntime.thenSome

/-- [bulksketch::decode::deg34::OMEGA]
    Source: 'src/decode/deg34.rs', lines 7:0-7:41 -/
@[global_simps, irreducible]
def decode.deg34.OMEGA : Std.U64 := 1858076378458151938#u64

/-- [bulksketch::decode::deg34::quadratic]:
    Source: 'src/decode/deg34.rs', lines 79:0-82:1 -/
def decode.deg34.quadratic
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (target : Std.U64) :
  Result (Option Std.U64)
  := do
  let o ←
    backendcontractBulkKernelsInst.ArithmeticInst.solve_quadratic target
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i ← backendcontractBulkKernelsInst.ArithmeticInst.square val
    let i1 ← lift (i ^^^ val)
    core.bool.Bool.then_some (i1 = target) val
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
      Std.U64 residual

/-- [bulksketch::decode::deg34::cubic]:
    Source: 'src/decode/deg34.rs', lines 95:0-109:1 -/
def decode.deg34.cubic
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (a : Std.U64) (b : Std.U64) (c : Std.U64) :
  Result (Option (Array Std.U64 3#usize))
  := do
  let i ← backendcontractBulkKernelsInst.ArithmeticInst.square a
  let p ← lift (i ^^^ b)
  let i1 ← backendcontractBulkKernelsInst.ArithmeticInst.mul a b
  let q ← lift (i1 ^^^ c)
  if q = 0#u64
  then ok none
  else
    let o ← backendcontractBulkKernelsInst.ArithmeticInst.inverse q
    let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i2 ← backendcontractBulkKernelsInst.ArithmeticInst.square p
      let i3 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i2 p
      let i4 ← backendcontractBulkKernelsInst.ArithmeticInst.square val
      let i5 ← backendcontractBulkKernelsInst.ArithmeticInst.mul i3 i4
      let o1 ←
        decode.deg34.quadratic fieldBinaryFieldInst
          backendcontractBulkKernelsInst i5
      let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let t ← backendcontractBulkKernelsInst.ArithmeticInst.mul q val1
        let q1 ← if t = 0#u64
                   then ok q
                   else ok t
        let o2 ←
          decode.deg34.cube_root fieldBinaryFieldInst
            backendcontractBulkKernelsInst q1
        let cf2 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          if p = 0#u64
          then
            let ou ←
              backendcontractBulkKernelsInst.ArithmeticInst.mul
                decode.deg34.OMEGA val2
            let ov ←
              backendcontractBulkKernelsInst.ArithmeticInst.mul
                decode.deg34.OMEGA 0#u64
            let i6 ← lift (a ^^^ val2)
            let i7 ← lift (i6 ^^^ 0#u64)
            let i8 ← lift (a ^^^ ou)
            let i9 ← lift (i8 ^^^ ov)
            let i10 ← lift (i9 ^^^ 0#u64)
            let i11 ← lift (a ^^^ ou)
            let i12 ← lift (i11 ^^^ val2)
            let i13 ← lift (i12 ^^^ ov)
            ok (some (Array.make 3#usize [ i7, i10, i13 ]))
          else
            let o3 ←
              backendcontractBulkKernelsInst.ArithmeticInst.inverse val2
            let cf3 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let v ←
                backendcontractBulkKernelsInst.ArithmeticInst.mul p val3
              let ou ←
                backendcontractBulkKernelsInst.ArithmeticInst.mul
                  decode.deg34.OMEGA val2
              let ov ←
                backendcontractBulkKernelsInst.ArithmeticInst.mul
                  decode.deg34.OMEGA v
              let i6 ← lift (a ^^^ val2)
              let i7 ← lift (i6 ^^^ v)
              let i8 ← lift (a ^^^ ou)
              let i9 ← lift (i8 ^^^ ov)
              let i10 ← lift (i9 ^^^ v)
              let i11 ← lift (a ^^^ ou)
              let i12 ← lift (i11 ^^^ val2)
              let i13 ← lift (i12 ^^^ ov)
              ok (some (Array.make 3#usize [ i7, i10, i13 ]))
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
                (Array Std.U64 3#usize) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
            (Array Std.U64 3#usize) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
          (Array Std.U64 3#usize) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
        (Array Std.U64 3#usize) residual

end bulksketch
