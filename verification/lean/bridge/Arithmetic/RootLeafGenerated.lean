-- Exact original leaf declaration with checked shared runtime bindings.
import Arithmetic.ClosedLeafGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::decode::roots::{bulksketch::decode::roots::Roots}::leaf]:
    Source: 'src/decode/roots.rs', lines 347:4-383:5 -/
def decode.roots.Roots.leaf
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
    decode.roots.charge meter (decode.work.Charge.Leaf self.degree)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    match self.degree.val with
    | 0 =>
      let roots := Array.repeat 2#usize 0#u64
      let s ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)) roots
          { «end» := self.degree }
      let b ← core.slice.Slice.contains core.cmp.PartialEqU64 s 0#u64
      if b
      then
        ok (core.result.Result.Ok (core.result.Result.Err
          types.DecodeFailure.InvalidLocator), self, workspace,
          fun workspace1 => workspace1, meter1)
      else
        let i ← self.count + self.degree
        let (s1, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
            workspace.roots { start := self.count, «end» := i }
        let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s1 s
        let s3 := index_mut_back s2
        let (s4, self1, workspace1, advance_back) ←
          decode.roots.Roots.advance { self with count := i }
            { workspace with roots := s3 }
        ok (core.result.Result.Ok (core.result.Result.Ok s4), self1,
          workspace1, advance_back, meter1)
    | 1 =>
      let i ← Slice.index_usize workspace.polynomials 0#usize
      let s ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64))
          (Array.make 2#usize [ i, 0#u64 ]) { «end» := self.degree }
      let b ← core.slice.Slice.contains core.cmp.PartialEqU64 s 0#u64
      if b
      then
        ok (core.result.Result.Ok (core.result.Result.Err
          types.DecodeFailure.InvalidLocator), self, workspace,
          fun workspace1 => workspace1, meter1)
      else
        let i1 ← self.count + self.degree
        let (s1, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
            workspace.roots { start := self.count, «end» := i1 }
        let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s1 s
        let s3 := index_mut_back s2
        let (s4, self1, workspace1, advance_back) ←
          decode.roots.Roots.advance { self with count := i1 }
            { workspace with roots := s3 }
        ok (core.result.Result.Ok (core.result.Result.Ok s4), self1,
          workspace1, advance_back, meter1)
    | 2 =>
      let linear ← Slice.index_usize workspace.polynomials 1#usize
      if linear = 0#u64
      then
        ok (core.result.Result.Ok (core.result.Result.Err
          types.DecodeFailure.NotSplit), self, workspace,
          fun workspace1 => workspace1, meter1)
      else
        let o ← backendcontractBulkKernelsInst.ArithmeticInst.inverse linear
        let inverse ←
          core.option.Option.expect o (toStr "nonzero quadratic coefficient")
        let i ← Slice.index_usize workspace.polynomials 0#usize
        let i1 ← backendcontractBulkKernelsInst.ArithmeticInst.square inverse
        let target ← backendcontractBulkKernelsInst.ArithmeticInst.mul i i1
        let o1 ←
          backendcontractBulkKernelsInst.ArithmeticInst.solve_quadratic target
        match o1 with
        | none =>
          ok (core.result.Result.Ok (core.result.Result.Err
            types.DecodeFailure.NotSplit), self, workspace,
            fun workspace1 => workspace1, meter1)
        | some solution =>
          let root ←
            backendcontractBulkKernelsInst.ArithmeticInst.mul linear solution
          let i2 ← lift (root ^^^ linear)
          let s ←
            core.array.Array.index (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64))
              (Array.make 2#usize [ root, i2 ]) { «end» := self.degree }
          let b ← core.slice.Slice.contains core.cmp.PartialEqU64 s 0#u64
          if b
          then
            ok (core.result.Result.Ok (core.result.Result.Err
              types.DecodeFailure.InvalidLocator), self, workspace,
              fun workspace1 => workspace1, meter1)
          else
            let i3 ← self.count + self.degree
            let (s1, index_mut_back) ←
              core.slice.index.Slice.index_mut
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U64)
                workspace.roots { start := self.count, «end» := i3 }
            let s2 ←
              core.slice.Slice.copy_from_slice core.marker.CopyU64 s1 s
            let s3 := index_mut_back s2
            let (s4, self1, workspace1, advance_back) ←
              decode.roots.Roots.advance { self with count := i3 }
                { workspace with roots := s3 }
            ok (core.result.Result.Ok (core.result.Result.Ok s4), self1,
              workspace1, advance_back, meter1)
    | _ => fail panic
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (core.result.Result types.Stage types.DecodeFailure)
        (core.convert.FromSame types.DecodeError) residual
    ok (r1, self, workspace, fun workspace1 => workspace1, meter1)

end bulksketch
