-- Exact original public report declarations from checked stock extraction.
import Arithmetic.PublicationWriteGenerated
import Arithmetic.MapsRuntime
import Arithmetic.ShapeWireRuntime

open Aeneas Aeneas.Std Result Error ControlFlow
set_option linter.dupNamespace false
set_option linter.unusedVariables false

noncomputable section

namespace bulksketch

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::DecodeReport<'_0>}::bucket_count]:
    Source: 'src/sketch/api.rs', lines 86:4-88:5
    Visibility: public -/
def sketch.api.DecodeReport.bucket_count
  (self : sketch.api.DecodeReport) : Result Std.Usize := do
  ok (Slice.len self.outcomes)

/-- [bulksketch::sketch::api::{bulksketch::sketch::api::DecodeReport<'_0>}::outcome]:
    Source: 'src/sketch/api.rs', lines 96:4-121:5
    Visibility: public -/
def sketch.api.DecodeReport.outcome
  (self : sketch.api.DecodeReport) (bucket : Std.Usize) :
  Result (Option sketch.api.DecodeOutcome)
  := do
  let o ←
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice
      sketch.api.StoredOutcome) self.outcomes bucket
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    match val.status with
    | sketch.api.OutcomeStatus.Unset => fail panic
    | sketch.api.OutcomeStatus.Equal =>
      ok (some sketch.api.DecodeOutcome.Equal)
    | sketch.api.OutcomeStatus.Decoded =>
      let r ←
        Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from val.start
      let start ←
        core.result.Result.expect
          core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
          "admitted result offset")
      let r1 ←
        Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from val.len
      let len ←
        core.result.Result.expect
          core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
          "admitted result length")
      let i ← start + len
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) self.ids
          { start, «end» := i }
      ok (some (sketch.api.DecodeOutcome.Decoded s))
    | sketch.api.OutcomeStatus.DegreeExceedsBudget =>
      ok (some (sketch.api.DecodeOutcome.Failed
        types.DecodeFailure.DegreeExceedsBudget))
    | sketch.api.OutcomeStatus.InvalidLocator =>
      ok (some (sketch.api.DecodeOutcome.Failed
        types.DecodeFailure.InvalidLocator))
    | sketch.api.OutcomeStatus.NotSplit =>
      ok (some (sketch.api.DecodeOutcome.Failed types.DecodeFailure.NotSplit))
    | sketch.api.OutcomeStatus.VerificationFailed =>
      ok (some (sketch.api.DecodeOutcome.Failed
        types.DecodeFailure.VerificationFailed))
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
      sketch.api.DecodeOutcome residual

end bulksketch
