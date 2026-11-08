-- Exact original-source declaration projection with existing scoped runtime bindings.
import Arithmetic.ReconstructionGenerated
import Arithmetic.QuarticGenerated
import Arithmetic.RebuiltLfsrGenerated
import Arithmetic.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive

/-- [bulksketch::decode::roots::charge]:
    Source: 'src/decode/roots.rs', lines 70:0-72:1 -/
def decode.roots.charge
  (meter : types.WorkMeter) (operation : decode.work.Charge) :
  Result ((core.result.Result Unit types.DecodeError) × types.WorkMeter)
  := do
  let r ← decode.work.WorkScheduleV1.cost operation
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    types.WorkMeter.charge meter val
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame types.DecodeError) residual
    ok (r1, meter)

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::stage]:
    Source: 'src/decode/roots.rs', lines 99:4-109:5 -/
def decode.roots.Roots.stage
  (self : decode.roots.Roots) : Result types.Stage := do
  if self.degree < 3#usize
  then ok types.Stage.Leaf
  else
    if self.closed_form
    then
      if self.degree = 3#usize
      then ok types.Stage.LeafThree
      else
        if self.closed_form
        then
          if self.degree = 4#usize
          then ok types.Stage.LeafFour
          else ok types.Stage.ReducerPreparation
        else ok types.Stage.ReducerPreparation
    else
      if self.closed_form
      then
        if self.degree = 4#usize
        then ok types.Stage.LeafFour
        else ok types.Stage.ReducerPreparation
      else ok types.Stage.ReducerPreparation

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::advance]:
    Source: 'src/decode/roots.rs', lines 110:4-127:5 -/
def decode.roots.Roots.advance
  (self : decode.roots.Roots) (workspace : decode.scratch.RowWorkspace) :
  Result (types.Stage × decode.roots.Roots × decode.scratch.RowWorkspace ×
    (decode.scratch.RowWorkspace → decode.scratch.RowWorkspace))
  := do
  if self.pending = 0#usize
  then
    ok (types.Stage.Verification, self, workspace,
      fun workspace1 => workspace1)
  else
    let i ← self.pending - 1#usize
    let frame ← Slice.index_usize workspace.stack i
    let r ←
      Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from
        frame.coefficient_start
    let start ←
      core.result.Result.expect
        core.num.error.TryFromIntError.Insts.CoreFmtDebug r (toStr
        "admitted coefficient offset")
    let r1 ←
      Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from
        frame.coefficient_len
    let len ←
      core.result.Result.expect
        core.num.error.TryFromIntError.Insts.CoreFmtDebug r1 (toStr
        "admitted coefficient length")
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
        workspace.polynomials { «end» := len }
    let i1 ← start + len
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U64) workspace.factors { start, «end» := i1 }
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s s1
    let i2 ← len - 1#usize
    let (i3, i4, s3) ←
      if self.affine
      then
        do
        let i5 ← start + self.stride
        let i6 ← i5 - 1#usize
        let i7 ← Slice.index_usize workspace.factors i6
        let i8 ← lift (UScalar.cast .Usize frame.next_direction)
        let s4 := index_mut_back s2
        ok (i7, i8, s4)
      else
        let s4 := index_mut_back s2
        ok (self.affine_base, self.affine_rank, s4)
    let s4 ←
      decode.roots.Roots.stage
        {
          self
            with
            pending := i,
            degree := i2,
            direction := frame.next_direction,
            checked := (frame.split_checked != 0#u32),
            affine_base := i3,
            affine_rank := i4
        }
    ok (s4,
      {
        self
          with
          pending := i,
          degree := i2,
          direction := frame.next_direction,
          checked := (frame.split_checked != 0#u32),
          affine_base := i3,
          affine_rank := i4
      }, { workspace with polynomials := s3 }, fun workspace1 => workspace1)

/-- [bulksketch::types::{impl core::cmp::PartialEq<bulksketch::types::Stage> for bulksketch::types::Stage}::eq]:
    Source: 'src/types.rs', lines 189:29-189:38
    Visibility: public -/
def types.Stage.Insts.CoreCmpPartialEqStage.eq
  (self : types.Stage) (other : types.Stage) : Result Bool := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

/-- Trait implementation: [bulksketch::types::{impl core::cmp::PartialEq<bulksketch::types::Stage> for bulksketch::types::Stage}]
    Source: 'src/types.rs', lines 189:29-189:38 -/
@[reducible]
impl_def types.Stage.Insts.CoreCmpPartialEqStage : core.cmp.PartialEq
  types.Stage types.Stage := {
  eq := types.Stage.Insts.CoreCmpPartialEqStage.eq
  ne := core.cmp.PartialEq.ne.trait_default
    types.Stage.Insts.CoreCmpPartialEqStage
}

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::closed_leaf]:
    Source: 'src/decode/roots.rs', lines 237:4-272:5 -/
def decode.roots.Roots.closed_leaf
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.roots.Roots) (stage : types.Stage)
  (workspace : decode.scratch.RowWorkspace) (meter : types.WorkMeter) :
  Result ((core.result.Result (core.result.Result types.Stage
    types.DecodeFailure) types.DecodeError) × decode.roots.Roots ×
    decode.scratch.RowWorkspace × (decode.scratch.RowWorkspace →
    decode.scratch.RowWorkspace) × types.WorkMeter)
  := do
  let b ←
    core.cmp.PartialEq.ne.trait_default types.Stage.Insts.CoreCmpPartialEqStage
      stage types.Stage.FactorVerification
  if b
  then
    if self.degree = 3#usize
    then
      let (r, meter1) ←
        decode.roots.charge meter decode.work.Charge.LeafThree
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let ((factor, rest), split_at_mut_back) ←
          core.slice.Slice.split_at_mut workspace.polynomials 11#usize
        let s ←
          core.slice.index.Slice.index
            (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U64) factor { «end» := self.degree }
        let (s1, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
            { «end» := 4#usize }
        let (o, s2) ←
          decode.deg34.solve fieldBinaryFieldInst
            backendcontractBulkKernelsInst s s1
        match o with
        | none =>
          let rest1 := index_mut_back s2
          let s3 := split_at_mut_back (factor, rest1)
          ok (core.result.Result.Ok (core.result.Result.Ok
            types.Stage.ReducerPreparation), self,
            { workspace with polynomials := s3 }, fun workspace1 => workspace1,
            meter1)
        | some count =>
          let rest1 := index_mut_back s2
          let s3 := split_at_mut_back (factor, rest1)
          ok (core.result.Result.Ok (core.result.Result.Ok
            types.Stage.FactorVerification),
            { self with solved_count := count },
            { workspace with polynomials := s3 }, fun workspace1 => workspace1,
            meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result types.Stage types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r1, self, workspace, fun workspace1 => workspace1, meter1)
    else
      let (r, meter1) ← decode.roots.charge meter decode.work.Charge.LeafFour
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let ((factor, rest), split_at_mut_back) ←
          core.slice.Slice.split_at_mut workspace.polynomials 11#usize
        let s ←
          core.slice.index.Slice.index
            (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U64) factor { «end» := self.degree }
        let (s1, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
            { «end» := 4#usize }
        let (o, s2) ←
          decode.deg34.solve fieldBinaryFieldInst
            backendcontractBulkKernelsInst s s1
        match o with
        | none =>
          let rest1 := index_mut_back s2
          let s3 := split_at_mut_back (factor, rest1)
          ok (core.result.Result.Ok (core.result.Result.Ok
            types.Stage.ReducerPreparation), self,
            { workspace with polynomials := s3 }, fun workspace1 => workspace1,
            meter1)
        | some count =>
          let rest1 := index_mut_back s2
          let s3 := split_at_mut_back (factor, rest1)
          ok (core.result.Result.Ok (core.result.Result.Ok
            types.Stage.FactorVerification),
            { self with solved_count := count },
            { workspace with polynomials := s3 }, fun workspace1 => workspace1,
            meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result types.Stage types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r1, self, workspace, fun workspace1 => workspace1, meter1)
  else
    let (r, meter1) ←
      decode.roots.charge meter (decode.work.Charge.FactorVerification
        self.degree)
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let ((values, product), split_at_mut_back) ←
        core.slice.Slice.split_at_mut workspace.polynomials 15#usize
      let i ← 11#usize + self.solved_count
      let roots ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) values
          { start := 11#usize, «end» := i }
      let s ←
        core.slice.index.Slice.index
          (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
          Std.U64) values { «end» := self.degree }
      let (s1, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) product
          { «end» := 5#usize }
      let (valid, s2) ←
        decode.deg34.certificate fieldBinaryFieldInst
          backendcontractBulkKernelsInst s roots s1
      if valid
      then
        let i1 ← self.count + self.degree
        let (s3, index_mut_back1) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
            workspace.roots { start := self.count, «end» := i1 }
        let s4 ←
          core.slice.Slice.copy_from_slice core.marker.CopyU64 s3 roots
        let product1 := index_mut_back s2
        let s5 := split_at_mut_back (values, product1)
        let s6 := index_mut_back1 s4
        let (s7, self1, workspace1, advance_back) ←
          decode.roots.Roots.advance { self with count := i1 }
            { workspace with polynomials := s5, roots := s6 }
        ok (core.result.Result.Ok (core.result.Result.Ok s7), self1,
          workspace1, advance_back, meter1)
      else
        let product1 := index_mut_back s2
        let s3 := split_at_mut_back (values, product1)
        ok (core.result.Result.Ok (core.result.Result.Ok
          types.Stage.ReducerPreparation), self,
          { workspace with polynomials := s3 }, fun workspace1 => workspace1,
          meter1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (core.result.Result types.Stage types.DecodeFailure)
          (core.convert.FromSame types.DecodeError) residual
      ok (r1, self, workspace, fun workspace1 => workspace1, meter1)

end bulksketch
