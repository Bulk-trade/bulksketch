-- Exact checked source projection. See extraction/root-divide for provenance.
import Arithmetic.RootSetupGenerated

open Aeneas Aeneas.Std Result Error

namespace Aeneas.Std.RootDivideRuntime

abbrev ExactDivide := ∀ {F K : Type}, bulksketch.field.BinaryField F →
    bulksketch.backend.contract.BulkKernels K F →
    Slice U64 → Slice U64 → Slice U64 → Slice U64 → Slice bulksketch.types.RawProduct →
    Result (Option Usize × Slice U64 × Slice U64 × Slice bulksketch.types.RawProduct)

/-- The scoped shared affine basis view is read-only. -/
def sharedOption {T : Type} (value : Option T) : Result (Option T) := .ok value

end Aeneas.Std.RootDivideRuntime

namespace bulksketch

variable (exactDivision : Aeneas.Std.RootDivideRuntime.ExactDivide)
local notation "poly.Dense.Insts.BulksketchPolyPolynomial.exact_divide_into" => exactDivision
local notation "core.option.Option.as_ref" => Aeneas.Std.RootDivideRuntime.sharedOption

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::divide]:
    Source: 'src/decode/roots.rs', lines 444:4-490:5 -/
def decode.roots.Roots.divide
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.roots.Roots) (buffers : decode.roots.FactorWork)
  (factors : Slice Std.U64) (stack : Slice decode.scratch.FactorFrame)
  (meter : types.WorkMeter) :
  Result ((core.result.Result (core.result.Result types.Stage
    types.DecodeFailure) types.DecodeError) × decode.roots.Roots ×
    decode.roots.FactorWork × (decode.roots.FactorWork →
    decode.roots.FactorWork) × (Slice Std.U64) × (Slice
    decode.scratch.FactorFrame) × types.WorkMeter)
  := do
  let (r, meter1) ←
    decode.roots.charge meter (decode.work.Charge.Divide self.degree)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let i ← self.degree + 2#usize
    let ((quotient, remainder), split_at_mut_back) ←
      core.slice.Slice.split_at_mut buffers.work i
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) buffers.gcd
        { «end» := self.gcd_len }
    let (o, quotient1, remainder1, s1) ←
      poly.Dense.Insts.BulksketchPolyPolynomial.exact_divide_into
        fieldBinaryFieldInst backendcontractBulkKernelsInst buffers.modulus s
        quotient remainder buffers.raw
    match o with
    | none =>
      let s2 := split_at_mut_back (quotient1, remainder1)
      ok (core.result.Result.Ok (core.result.Result.Err
        types.DecodeFailure.InvalidLocator), self,
        { buffers with work := s2, raw := s1 }, fun buffers1 => buffers1,
        factors, stack, meter1)
    | some len =>
      let (r1, meter2) ←
        decode.roots.charge meter1 (decode.work.Charge.SplitAssembly
          self.degree)
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let o1 ← lift (Usize.checked_mul self.pending self.stride)
        let r2 ←
          core.option.Option.ok_or o1 types.DecodeError.ScratchTooSmall
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let o2 ← lift (Usize.checked_add val len)
          let r3 ←
            core.option.Option.ok_or o2 types.DecodeError.ScratchTooSmall
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            let (s2, index_mut_back) ←
              core.slice.index.Slice.index_mut
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) factors
                { start := val, «end» := val1 }
            let s3 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                quotient1 { «end» := len }
            let s4 ←
              core.slice.Slice.copy_from_slice core.marker.CopyU64 s2 s3
            let r4 ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from val
            let i1 ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r4 (toStr
                "admitted offset")
            let r5 ←
              U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from len
            let i2 ←
              core.result.Result.expect
                core.num.error.TryFromIntError.Insts.CoreFmtDebug r5 (toStr
                "admitted degree")
            let i3 ← self.direction + 1#u32
            let (_, index_mut_back1) ←
              Slice.index_mut_usize stack self.pending
            let (i4, sb, factors1, stack1) ←
              if self.affine
              then
                do
                let i5 ← self.affine_rank - 1#usize
                let o3 ← core.option.Option.as_ref buffers.basis.directions
                let a ← core.option.Option.expect o3 (toStr "affine basis")
                let i6 ← Array.index_usize a i5
                let i7 ← val + self.stride
                let i8 ← i7 - 1#usize
                let factors2 := index_mut_back s4
                let i9 ← lift (self.affine_base ^^^ i6)
                let s5 ← Slice.update factors2 i8 i9
                let stack2 :=
                  index_mut_back1
                    {
                      coefficient_start := i1,
                      coefficient_len := i2,
                      next_direction := i3,
                      split_checked := 1#u32
                    }
                let (ff, index_mut_back2) ←
                  Slice.index_mut_usize stack2 self.pending
                let i10 ← lift (UScalar.cast .U32 i5)
                let s6 := index_mut_back2 { ff with next_direction := i10 }
                ok (i5, buffers.basis, s5, s6)
              else
                let factors2 := index_mut_back s4
                let s5 :=
                  index_mut_back1
                    {
                      coefficient_start := i1,
                      coefficient_len := i2,
                      next_direction := i3,
                      split_checked := 1#u32
                    }
                ok (self.affine_rank, buffers.basis, factors2, s5)
            let i5 ← self.pending + 1#usize
            let (s5, index_mut_back2) ←
              core.slice.index.Slice.index_mut
                (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
                buffers.modulus { «end» := self.gcd_len }
            let s6 ←
              core.slice.Slice.copy_from_slice core.marker.CopyU64 s5 s
            let s7 ←
              decode.roots.Roots.stage
                {
                  self
                    with
                    pending := i5,
                    degree := self.gcd_degree,
                    direction := i3,
                    checked := true,
                    affine_rank := i4
                }
            let s8 := index_mut_back2 s6
            let s9 := split_at_mut_back (quotient1, remainder1)
            ok (core.result.Result.Ok (core.result.Result.Ok s7),
              {
                self
                  with
                  pending := i5,
                  degree := self.gcd_degree,
                  direction := i3,
                  checked := true,
                  affine_rank := i4
              },
              { buffers with modulus := s8, work := s9, raw := s1, basis := sb
              }, fun buffers1 => buffers1, factors1, stack1, meter2)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r4 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                (core.result.Result types.Stage types.DecodeFailure)
                (core.convert.FromSame types.DecodeError) residual
            let s2 := split_at_mut_back (quotient1, remainder1)
            ok (r4, self, { buffers with work := s2, raw := s1 },
              fun buffers1 => buffers1, factors, stack, meter2)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (core.result.Result types.Stage types.DecodeFailure)
              (core.convert.FromSame types.DecodeError) residual
          let s2 := split_at_mut_back (quotient1, remainder1)
          ok (r3, self, { buffers with work := s2, raw := s1 },
            fun buffers1 => buffers1, factors, stack, meter2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result types.Stage types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        let s2 := split_at_mut_back (quotient1, remainder1)
        ok (r2, self, { buffers with work := s2, raw := s1 },
          fun buffers1 => buffers1, factors, stack, meter2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (core.result.Result types.Stage types.DecodeFailure)
        (core.convert.FromSame types.DecodeError) residual
    ok (r1, self, buffers, fun buffers1 => buffers1, factors, stack, meter1)

end bulksketch
