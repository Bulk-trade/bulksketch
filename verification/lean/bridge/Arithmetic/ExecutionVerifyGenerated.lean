-- Original Execution::verify declaration with imports of separately checked callees.
import Arithmetic.DegreeProbeGenerated
import Arithmetic.VerifyDispatchGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::verify]:
    Source: 'src/decode/stages.rs', lines 334:4-372:5 -/
def decode.stages.Execution.verify
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) (input : decode.row.RowInput)
  (workspace : decode.scratch.RowWorkspace) (meter : types.WorkMeter) :
  Result ((core.result.Result (core.result.Result (Option types.Stage)
    types.DecodeFailure) types.DecodeError) × (decode.stages.Execution F K) ×
    decode.scratch.RowWorkspace × (decode.scratch.RowWorkspace →
    decode.scratch.RowWorkspace) × types.WorkMeter)
  := do
  let capacity := Slice.len input.difference
  let (r, lfsr) ←
    if self.v3
    then
      do
      let lfsr1 ← decode.verify.use_rebuilt_lfsr self.roots.count capacity
      ok (self.roots, lfsr1)
    else ok (self.roots, false)
  let (r1, operation) ←
    if lfsr
    then
      ok (r, decode.work.Charge.VerifyLfsr capacity self.budget.total r.count)
    else ok (r, decode.work.Charge.Verify capacity self.budget.total)
  let (r2, meter1) ←
    decode.stages.Execution.charge fieldBinaryFieldInst
      backendcontractBulkKernelsInst meter operation
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r2
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let roots ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) workspace.roots
        { «end» := r1.count }
    let (s, s1, valid) ←
      if lfsr
      then
        do
        let (valid1, s2, s3) ←
          decode.verify.rebuilt_lfsr fieldBinaryFieldInst
            backendcontractBulkKernelsInst roots input.difference workspace.bm
            workspace.verification
        ok (s2, s3, valid1)
      else
        do
        let (valid1, s2) ←
          decode.probe.verified fieldBinaryFieldInst
            backendcontractBulkKernelsInst input.difference roots
            workspace.verification
        ok (workspace.bm, s2, valid1)
    if valid
    then
      ok (core.result.Result.Ok (core.result.Result.Ok (some
        types.Stage.Canonicalization)), { self with roots := r1 },
        { workspace with bm := s, verification := s1 },
        fun workspace1 => workspace1, meter1)
    else
      ok (core.result.Result.Ok (core.result.Result.Err
        types.DecodeFailure.VerificationFailed), { self with roots := r1 },
        { workspace with bm := s, verification := s1 },
        fun workspace1 => workspace1, meter1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r3 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (core.result.Result (Option types.Stage) types.DecodeFailure)
        (core.convert.FromSame types.DecodeError) residual
    ok (r3, { self with roots := r1 }, workspace, fun workspace1 => workspace1,
      meter1)

end bulksketch
