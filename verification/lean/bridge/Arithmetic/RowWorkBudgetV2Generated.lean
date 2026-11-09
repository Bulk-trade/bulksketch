-- Original checked V2 row wrapper carrying the V1 sum-cost parameter.
import Arithmetic.RowWorkBudgetGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

/-- [bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV2}::row_bound]:
    Source: 'src/decode/work.rs', lines 265:4-290:5 -/
def decode.work.WorkScheduleV2.row_bound
  (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity : Std.Usize) (budget : Std.Usize) (beta : Std.Usize)
  (candidates : Std.Usize) :
  Result (core.result.Result types.WorkUnits types.DecodeError)
  := do
  let r ←
    decode.work.WorkScheduleV1.row_bound sumCosts capacity budget beta candidates
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      decode.work.WorkScheduleV1.cost (decode.work.Charge.Verify capacity beta)
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      if budget >= 1#usize
      then
        let r2 ← decode.work.WorkScheduleV1.cost decode.work.Charge.DirectOne
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let r3 ← decode.work.add val2 val1
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let r4 ← decode.work.add val val3
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              if capacity >= 2#usize
              then
                if budget >= 2#usize
                then
                  let r5 ←
                    decode.work.WorkScheduleV1.cost
                      decode.work.Charge.DirectTwo
                  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue val5 =>
                    let r6 ← decode.work.add val5 val1
                    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue val6 =>
                      let r7 ← decode.work.add val4 val6
                      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue val7 =>
                        ok (core.result.Result.Ok val7)
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
                else ok (core.result.Result.Ok val4)
              else ok (core.result.Result.Ok val4)
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      else
        if capacity >= 2#usize
        then
          if budget >= 2#usize
          then
            let r2 ←
              decode.work.WorkScheduleV1.cost decode.work.Charge.DirectTwo
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue val2 =>
              let r3 ← decode.work.add val2 val1
              let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue val3 =>
                let r4 ← decode.work.add val val3
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  ok (core.result.Result.Ok val4)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    types.WorkUnits (core.convert.FromSame types.DecodeError)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  types.WorkUnits (core.convert.FromSame types.DecodeError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          else ok (core.result.Result.Ok val)
        else ok (core.result.Result.Ok val)
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      types.WorkUnits (core.convert.FromSame types.DecodeError) residual

end bulksketch
