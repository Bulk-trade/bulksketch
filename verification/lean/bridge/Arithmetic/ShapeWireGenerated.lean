-- Exact original source declaration. Only imports and scoped std bindings are adapted.
module
public import Arithmetic.ShapeWireRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::sketch::shape::record_bytes]:
    Source: 'src/sketch/shape.rs', lines 120:0-127:1 -/
def sketch.shape.record_bytes
  (buckets : Std.Usize) (words : Std.Usize) : Result (Option Std.Usize) := do
  let o ← lift (Usize.checked_mul buckets 2#usize)
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let o1 ← lift (Usize.checked_add buckets 7#usize)
    let cf1 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let o2 ← lift (Usize.checked_div val1 8#usize)
      let cf2 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let o3 ← lift (Usize.checked_mul words 8#usize)
        let cf3 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let o4 ← lift (Usize.checked_add val3 val2)
          let cf4 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let r ←
              core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from val
            let o5 ← core.result.Result.ok r
            let cf5 ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r1 ←
                core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
                  val4
              let o6 ← core.result.Result.ok r1
              let cf6 ←
                core.option.Option.Insts.CoreOpsTry_traitTry.branch o6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let o7 ← lift (Usize.checked_add 24#usize val)
                let cf7 ←
                  core.option.Option.Insts.CoreOpsTry_traitTry.branch o7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val5 =>
                  ok (Usize.checked_add val5 val4)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
                    Std.Usize residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
                  Std.Usize residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
                Std.Usize residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
              Std.Usize residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
            Std.Usize residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
          Std.Usize residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
        Std.Usize residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
      Std.Usize residual

end bulksketch
