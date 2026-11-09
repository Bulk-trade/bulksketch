-- Checked original row_bound projection with the explicit captured sum_costs slot.
import Arithmetic.RootWorkBudgetGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace Aeneas.Std.RowWorkBudgetRuntime

abbrev SumCosts := Slice bulksketch.decode.work.Charge →
  Result (core.result.Result U64 bulksketch.types.DecodeError)

end Aeneas.Std.RowWorkBudgetRuntime

noncomputable section

namespace bulksketch

variable (sumCosts : RowWorkBudgetRuntime.SumCosts)
local notation "decode.work.sum_costs" => sumCosts

/-- [bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV1}::row_bound]:
    Source: 'src/decode/work.rs', lines 230:4-258:5 -/
def decode.work.WorkScheduleV1.row_bound
  (capacity : Std.Usize) (budget : Std.Usize) (beta : Std.Usize)
  (candidates : Std.Usize) :
  Result (core.result.Result types.WorkUnits types.DecodeError)
  := do
  let s ←
    lift (Array.to_slice
      (Array.make 6#usize [
        decode.work.Charge.Compare capacity, decode.work.Charge.Reconstruct
        capacity, decode.work.Charge.Candidates budget candidates,
        decode.work.Charge.Deflate budget, decode.work.Charge.Verify capacity
        beta, decode.work.Charge.Canonicalize beta
        ]))
  let r ← decode.work.sum_costs s
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← decode.work.number capacity
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ← decode.work.mul 2#u64 val1
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r3 ←
          decode.work.WorkScheduleV1.cost (decode.work.Charge.BmStep budget)
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r4 ← decode.work.mul val2 val3
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let r5 ← decode.work.add val val4
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let r6 ← decode.work.WorkScheduleV1.roots_bound budget
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val6 =>
                let r7 ← decode.work.add val5 val6
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val7 =>
                  ok (core.result.Result.Ok val7)
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
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              types.WorkUnits (core.convert.FromSame types.DecodeError)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      types.WorkUnits (core.convert.FromSame types.DecodeError) residual

end bulksketch
