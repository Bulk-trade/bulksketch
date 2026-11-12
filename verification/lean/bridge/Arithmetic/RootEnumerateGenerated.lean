-- Original checked source projection for Roots::enumerate_affine.
import Arithmetic.ClosedLeafGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace Aeneas.Std.RootEnumerateRuntime

open bulksketch

/-- Explicit original affine enumeration call. -/
abbrev Enumerate := ∀ {F K : Type}, field.BinaryField F → backend.contract.BulkKernels K F →
  Slice U64 → U64 → Slice U64 → Slice U64 → Slice U64 →
    Result (core.result.Result Usize types.DecodeFailure × Slice U64 × Slice U64)

/-- Shared Rust Option view preserves the tag and payload. -/
def optionAsRef {T : Type} (value : Option T) : Result (Option T) := .ok value

end Aeneas.Std.RootEnumerateRuntime

namespace bulksketch

variable (enumerateModel : RootEnumerateRuntime.Enumerate)

local notation "decode.affine.enumerate" => enumerateModel
local notation "core.option.Option.as_ref" => RootEnumerateRuntime.optionAsRef
local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::enumerate_affine]:
    Source: 'src/decode/roots.rs', lines 321:4-345:5 -/
def decode.roots.Roots.enumerate_affine
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.roots.Roots) (workspace : decode.scratch.RowWorkspace)
  (meter : types.WorkMeter) :
  Result ((core.result.Result (core.result.Result types.Stage
    types.DecodeFailure) types.DecodeError) × decode.roots.Roots ×
    decode.scratch.RowWorkspace × (decode.scratch.RowWorkspace →
    decode.scratch.RowWorkspace) × types.WorkMeter)
  := do
  let (r, meter1) ←
    decode.roots.charge meter (decode.work.Charge.AffineEnumeration self.degree
      self.affine_rank)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let s ←
      core.slice.index.Slice.index
        (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
        Std.U64) workspace.polynomials { «end» := self.degree }
    let o ← core.option.Option.as_ref workspace.basis.directions
    let a ← core.option.Option.expect o (toStr "affine basis")
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)) a
        { «end» := self.affine_rank }
    let (s2, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U64)
        workspace.roots { start := self.count }
    let (r1, s3, s4) ←
      decode.affine.enumerate fieldBinaryFieldInst
        backendcontractBulkKernelsInst s self.affine_base s1 s2 workspace.bm
    match r1 with
    | core.result.Result.Ok count =>
      let i ← self.count + count
      let s5 := index_mut_back s3
      let (s6, self1, workspace1, advance_back) ←
        decode.roots.Roots.advance { self with count := i }
          { workspace with bm := s4, roots := s5 }
      ok (core.result.Result.Ok (core.result.Result.Ok s6), self1, workspace1,
        advance_back, meter1)
    | core.result.Result.Err reason =>
      let s5 := index_mut_back s3
      ok (core.result.Result.Ok (core.result.Result.Err reason), self,
        { workspace with bm := s4, roots := s5 }, fun workspace1 => workspace1,
        meter1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (core.result.Result types.Stage types.DecodeFailure)
        (core.convert.FromSame types.DecodeError) residual
    ok (r1, self, workspace, fun workspace1 => workspace1, meter1)
end bulksketch
