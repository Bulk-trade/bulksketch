-- Original checked public DecodeExecution result dispatch.
import Arithmetic.RowDispatchGenerated
import Arithmetic.CompletedResultGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (dictionaries : RowDispatchRuntime.Dictionaries)
local notation "backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels" => dictionaries.portable
local notation "backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels" => dictionaries.pclmul
local notation "backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels" => dictionaries.vpclmul512

/-- [bulksketch::sketch::dispatch::{bulksketch::sketch::dispatch::DecodeExecution<F>}::completed_result]:
    Source: 'src/sketch/dispatch.rs', lines 171:4-186:5 -/
def sketch.dispatch.DecodeExecution.completed_result
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.dispatch.DecodeExecution F)
  (workspace : decode.scratch.RowWorkspace) :
  Result (core.result.Result decode.row.RowResult types.DecodeError)
  := do
  match self with
  | sketch.dispatch.DecodeExecution.Probe probe _ =>
    let o ← decode.probe.Probe.next_stage probe
    let b := core.option.Option.is_none o
    massert b
    let i ← decode.probe.Probe.impl.count probe
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) workspace.roots
        { «end» := i }
    ok (core.result.Result.Ok (decode.row.RowResult.Decoded s))
  | sketch.dispatch.DecodeExecution.Portable row =>
    decode.stages.Execution.completed_result fieldBinaryFieldInst
      (backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) row workspace
  | sketch.dispatch.DecodeExecution.Pclmul row =>
    decode.stages.Execution.completed_result fieldBinaryFieldInst
      (backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) row workspace
  | sketch.dispatch.DecodeExecution.Vpclmul512 row =>
    decode.stages.Execution.completed_result fieldBinaryFieldInst
      (backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
      fieldBinaryFieldInst) row workspace

end bulksketch
