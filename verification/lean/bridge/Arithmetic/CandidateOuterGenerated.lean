-- Original checked candidate entry and outer chunk declarations.
import Arithmetic.CandidateInnerGenerated
import Arithmetic.CandidateDenseEvalGenerated
import Arithmetic.ReconstructionTypes
import Arithmetic.WorkScheduleGenerated
import Arithmetic.AvxHornerChunkRuntime
import Arithmetic.RootSetupGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

local notation "core.slice.iter.Chunks" => AvxHornerChunkRuntime.ChunkState
local notation "core.slice.Slice.chunks" => AvxHornerChunkRuntime.chunks
local notation "core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next" =>
  AvxHornerChunkRuntime.nextShared
local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive
local notation "core.iter.traits.iterator.Iterator.zip.trait_default" =>
  Aeneas.Std.core.iter.traits.iterator.Iterator.zip.trait_default

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::candidates]: loop body 0:
    Source: 'src/decode/stages.rs', lines 285:8-303:5 -/
@[rust_loop_body]
def decode.stages.Execution.candidates_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (i : Std.Usize) (locator : Slice Std.U64)
  (iter : core.slice.iter.Chunks Std.U64) (i1 : Std.Usize) (s : Slice Std.U64)
  (values : Slice Std.U64) (return_from_inner : Bool) :
  Result (ControlFlow ((core.slice.iter.Chunks Std.U64) × Std.Usize × (Slice
    Std.U64) × (Slice Std.U64) × Bool) (Std.Usize × (Slice Std.U64) ×
    (Slice Std.U64) × Bool))
  := do
  let (o, iter1) ←
    core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
      iter
  match o with
  | none => ok (done (i1, s, values, return_from_inner))
  | some points =>
    let s1 ←
      core.slice.index.Slice.index
        (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
        Std.U64) locator { «end» := i }
    let i2 := Slice.len points
    let (s2, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) values
        { «end» := i2 }
    let s3 ←
      poly.Dense.Insts.BulksketchPolyPolynomial.eval_many_into
        fieldBinaryFieldInst backendcontractBulkKernelsInst s1 points s2
    let i3 ← core.slice.Slice.iter points
    let values1 := index_mut_back s3
    let i4 ← core.slice.Slice.iter values1
    let iter2 ←
      core.iter.traits.iterator.Iterator.zip.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U64)
        (core.iter.traits.collect.IntoIterator.Blanket
        (core.iter.traits.iterator.IteratorSliceIter Std.U64)) i3 i4
    let (i5, s4, return_from_inner1) ←
      decode.stages.Execution.candidates_loop0_loop0 iter2 i i1 s
        return_from_inner
    if return_from_inner1
    then ok (done (i5, s4, values1, return_from_inner1))
    else ok (cont (iter1, i5, s4, values1, return_from_inner1))

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::candidates]: loop 0:
    Source: 'src/decode/stages.rs', lines 285:8-303:5 -/
@[rust_loop]
def decode.stages.Execution.candidates_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.slice.iter.Chunks Std.U64) (i : Std.Usize) (i1 : Std.Usize)
  (s : Slice Std.U64) (locator : Slice Std.U64) (values : Slice Std.U64)
  (return_from_inner : Bool) :
  Result (Std.Usize × (Slice Std.U64) × (Slice Std.U64) × Bool)
  := do
  loop
    (fun (iter1, i2, s1, values1, return_from_inner1) =>
      decode.stages.Execution.candidates_loop0.body fieldBinaryFieldInst
      backendcontractBulkKernelsInst i locator iter1 i2 s1 values1
      return_from_inner1)
    (iter, i1, s, values, return_from_inner)

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::candidates]:
    Source: 'src/decode/stages.rs', lines 266:4-303:5 -/
def decode.stages.Execution.candidates
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
  let i := Slice.len input.candidates
  let (r, meter1) ←
    decode.stages.Execution.charge fieldBinaryFieldInst
      backendcontractBulkKernelsInst meter (decode.work.Charge.Candidates
      self.degree i)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let width ← capacity + 1#usize
    let ((locator, rest), split_at_mut_back) ←
      core.slice.Slice.split_at_mut workspace.bm width
    let (values, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
        { «end» := width }
    let iter ← core.slice.Slice.chunks input.candidates width
    let (i1, s, values1, return_from_inner) ←
      decode.stages.Execution.candidates_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst iter self.degree self.hits
        workspace.roots locator values false
    if return_from_inner
    then
      let rest1 := index_mut_back values1
      let s1 := split_at_mut_back (locator, rest1)
      ok (core.result.Result.Ok (core.result.Result.Err
        types.DecodeFailure.InvalidLocator), { self with hits := i1 },
        { workspace with bm := s1, roots := s }, fun workspace1 => workspace1,
        meter1)
    else
      let rest1 := index_mut_back values1
      let s1 := split_at_mut_back (locator, rest1)
      ok (core.result.Result.Ok (core.result.Result.Ok (some
        types.Stage.Deflation)),
        { self with hits := i1, roots := { self.roots with count := i1 } },
        { workspace with bm := s1, roots := s }, fun workspace1 => workspace1,
        meter1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (core.result.Result (Option types.Stage) types.DecodeFailure)
        (core.convert.FromSame types.DecodeError) residual
    ok (r1, self, workspace, fun workspace1 => workspace1, meter1)

end bulksketch
