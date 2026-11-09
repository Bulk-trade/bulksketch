-- Exact stock original Roots::prepare_affine with typed algorithm slots.
import Arithmetic.ClosedLeafGenerated
import Arithmetic.AffineSubspacesGenerated
import Arithmetic.WorkScheduleRuntime
import Arithmetic.RebuiltLfsrRuntime

open Aeneas Aeneas.Std Result Error

namespace Aeneas.Std.RootAffinePreparationRuntime

open bulksketch

structure Callees where
  multiple : ∀ {F K : Type}, field.BinaryField F → backend.contract.BulkKernels K F →
    Slice U64 → Slice U64 → Slice U64 → Slice U64 → Slice U64 → Slice types.RawProduct →
    Result (Usize × Slice U64 × Slice U64 × Slice U64 × Slice types.RawProduct)
  solveMap : ∀ {F K : Type}, field.BinaryField F → backend.contract.BulkKernels K F →
    Slice U64 → Array U64 64#usize → Result (Option (U64 × Usize) × Array U64 64#usize)
  enumeratePreferred : Usize → Usize → Result Bool

/-- Option insertion for the Copy array of GF64 direction words. -/
def insertBasis (_old : Option (Array U64 64#usize)) (value : Array U64 64#usize) :
    Result (Array U64 64#usize × (Array U64 64#usize → Option (Array U64 64#usize))) :=
  .ok (value, some)

end Aeneas.Std.RootAffinePreparationRuntime

namespace bulksketch

variable (calls : RootAffinePreparationRuntime.Callees)

set_option linter.unusedVariables false

local notation "core.option.Option.insert" => RootAffinePreparationRuntime.insertBasis
local notation "decode.affine.multiple" => calls.multiple
local notation "decode.affine.solve_map" => calls.solveMap
local notation "decode.affine.enumerate_preferred" => calls.enumeratePreferred
local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::prepare_affine::{closure}]
    Source: 'src/decode/roots.rs', lines 304:29-304:50 -/
@[reducible]
def decode.roots.Roots.prepare_affine.closure (F : Type _) (K : Type _) :=
  Std.Usize

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::prepare_affine::{impl core::ops::function::FnOnce<(u64,), bool> for bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::prepare_affine::{closure}<'_0, F, K>}::call_once]:
    Source: 'src/decode/roots.rs', lines 304:29-304:50 -/
def
  decode.roots.Roots.prepare_affine.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.roots.Roots.prepare_affine.closure F K) (tupled_args : Std.U64) :
  Result Bool
  := do
  let i ← lift (UScalar.cast .U64 c)
  ok (tupled_args < i)

/-- Trait implementation: [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::prepare_affine::{impl core::ops::function::FnOnce<(u64,), bool> for bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::prepare_affine::{closure}<'_0, F, K>}]
    Source: 'src/decode/roots.rs', lines 304:29-304:50 -/
@[reducible]
def
  decode.roots.Roots.prepare_affine.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.roots.Roots.prepare_affine.closure F K)
  Std.U64 Bool := {
  call_once :=
    decode.roots.Roots.prepare_affine.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::prepare_affine]:
    Source: 'src/decode/roots.rs', lines 274:4-319:5 -/
def decode.roots.Roots.prepare_affine
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
    decode.roots.charge meter (decode.work.Charge.AffinePreparation
      self.degree)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let i ← self.degree + 1#usize
    let ((coefficients, work), split_at_mut_back) ←
      core.slice.Slice.split_at_mut workspace.bm i
    let s ←
      core.slice.index.Slice.index
        (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
        Std.U64) workspace.polynomials { «end» := self.degree }
    let i1 ← self.degree / 2#usize
    let i2 ← self.degree * i1
    let s1 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
        workspace.square_table { «end» := i2 }
    let (len, s2, coefficients1, work1, s3) ←
      decode.affine.multiple fieldBinaryFieldInst
        backendcontractBulkKernelsInst s s1 workspace.factors coefficients work
        workspace.raw
    let i3 ← Slice.index_usize coefficients1 1#usize
    if i3 = 0#u64
    then
      let s4 := split_at_mut_back (coefficients1, work1)
      ok (core.result.Result.Ok (core.result.Result.Err
        types.DecodeFailure.NotSplit), self,
        { workspace with bm := s4, factors := s2, raw := s3 },
        fun workspace1 => workspace1, meter1)
    else
      let a := Array.repeat 64#usize 0#u64
      let (basis, insert_back) ←
        core.option.Option.insert workspace.basis.directions a
      let s4 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) coefficients1
          { «end» := len }
      let (o, basis1) ←
        decode.affine.solve_map fieldBinaryFieldInst
          backendcontractBulkKernelsInst s4 basis
      match o with
      | none =>
        let s5 := split_at_mut_back (coefficients1, work1)
        let o1 := insert_back basis1
        ok (core.result.Result.Ok (core.result.Result.Err
          types.DecodeFailure.NotSplit), self,
          {
            workspace
              with
              bm := s5,
              factors := s2,
              raw := s3,
              basis := { workspace.basis with directions := o1 }
          }, fun workspace1 => workspace1, meter1)
      | some p =>
        let (base, rank) := p
        let i4 ← len - 1#usize
        if rank >= i4
        then
          let s5 := split_at_mut_back (coefficients1, work1)
          let o1 := insert_back basis1
          ok (core.result.Result.Ok (core.result.Result.Err
            types.DecodeFailure.NotSplit), self,
            {
              workspace
                with
                bm := s5,
                factors := s2,
                raw := s3,
                basis := { workspace.basis with directions := o1 }
            }, fun workspace1 => workspace1, meter1)
        else
          let i5 ← lift (UScalar.cast .U32 rank)
          let o1 ← core.num.U64.checked_shl 1#u64 i5
          let b ←
            core.option.Option.is_some_and
              (decode.roots.Roots.prepare_affine.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool
              fieldBinaryFieldInst backendcontractBulkKernelsInst) o1
              self.degree
          if b
          then
            let s5 := split_at_mut_back (coefficients1, work1)
            let o2 := insert_back basis1
            ok (core.result.Result.Ok (core.result.Result.Err
              types.DecodeFailure.NotSplit), self,
              {
                workspace
                  with
                  bm := s5,
                  factors := s2,
                  raw := s3,
                  basis := { workspace.basis with directions := o2 }
              }, fun workspace1 => workspace1, meter1)
          else
            let i6 ← lift (UScalar.cast .U32 rank)
            let b1 ← decode.affine.enumerate_preferred self.degree rank
            if b1
            then
              let s5 := split_at_mut_back (coefficients1, work1)
              let o2 := insert_back basis1
              ok (core.result.Result.Ok (core.result.Result.Ok
                types.Stage.AffineEnumeration),
                {
                  self
                    with
                    affine_ready := true,
                    affine_base := base,
                    affine_rank := rank
                },
                {
                  workspace
                    with
                    bm := s5,
                    factors := s2,
                    raw := s3,
                    basis := { directions := o2, len := i6 }
                }, fun workspace1 => workspace1, meter1)
            else
              let offset ← self.stride * self.stride
              let s5 ←
                core.array.Array.index (core.ops.index.IndexSlice
                  (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64))
                  basis1 { «end» := rank }
              let (s6, index_mut_back) ←
                core.slice.index.Slice.index_mut
                  (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U64) s2
                  { start := offset }
              let s7 ←
                decode.affine.subspaces fieldBinaryFieldInst
                  backendcontractBulkKernelsInst s5 s6
              let s8 := split_at_mut_back (coefficients1, work1)
              let s9 := index_mut_back s7
              let o2 := insert_back basis1
              ok (core.result.Result.Ok (core.result.Result.Ok
                types.Stage.AffineSplit),
                {
                  self
                    with
                    affine_ready := true,
                    affine_base := base,
                    affine_rank := rank
                },
                {
                  workspace
                    with
                    bm := s8,
                    factors := s9,
                    raw := s3,
                    basis := { directions := o2, len := i6 }
                }, fun workspace1 => workspace1, meter1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (core.result.Result types.Stage types.DecodeFailure)
        (core.convert.FromSame types.DecodeError) residual
    ok (r1, self, workspace, fun workspace1 => workspace1, meter1)

end bulksketch
