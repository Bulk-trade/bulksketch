-- Original checked completed-result projection preserving the shared roots prefix.
import Arithmetic.ReconstructionTypes

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace bulksketch

/-- [bulksketch::decode::row::RowResult]
    Source: 'src/decode/row.rs', lines 16:0-20:1 -/
@[discriminant isize]
inductive decode.row.RowResult where
| Equal : decode.row.RowResult
| Decoded : Slice Std.U64 → decode.row.RowResult
| Failed : types.DecodeFailure → decode.row.RowResult

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::completed_result]:
    Source: 'src/decode/stages.rs', lines 142:4-157:5 -/
def decode.stages.Execution.completed_result
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K)
  (workspace : decode.scratch.RowWorkspace) :
  Result (core.result.Result decode.row.RowResult types.DecodeError)
  := do
  match self.state with
  | decode.stages.State.Running _ => fail panic
  | decode.stages.State.Complete =>
    if self.roots.count = 0#usize
    then
      if self.budget.total = self.budget.nonzero
      then ok (core.result.Result.Ok decode.row.RowResult.Equal)
      else
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
            workspace.roots { «end» := self.roots.count }
        ok (core.result.Result.Ok (decode.row.RowResult.Decoded s))
    else
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
          workspace.roots { «end» := self.roots.count }
      ok (core.result.Result.Ok (decode.row.RowResult.Decoded s))
  | decode.stages.State.Failed reason =>
    ok (core.result.Result.Ok (decode.row.RowResult.Failed reason))
  | decode.stages.State.Error error => ok (core.result.Result.Err error)

end bulksketch
