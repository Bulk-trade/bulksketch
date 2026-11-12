-- Checked original deflate projection with the scoped return-join retry.
import Arithmetic.ExecutionVerifyGenerated
import Arithmetic.RootSetupGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 4096
set_option linter.unusedVariables false

namespace bulksketch

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::deflate]: loop body 1:
    Source: 'src/decode/stages.rs', lines 323:12-325:13 -/
@[rust_loop_body]
def decode.stages.Execution.deflate_loop0_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (locator : Slice Std.U64) (root : Std.U64)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (quotient : Slice Std.U64) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × (Slice Std.U64)) (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done quotient)
  | some i =>
    let i1 ← Slice.index_usize locator i
    let i2 ← Slice.index_usize quotient i
    let i3 ← backendcontractBulkKernelsInst.ArithmeticInst.mul root i2
    let i4 ← i - 1#usize
    let i5 ← lift (i1 ^^^ i3)
    let s ← Slice.update quotient i4 i5
    ok (cont (iter1, s))

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::deflate]: loop 1:
    Source: 'src/decode/stages.rs', lines 323:12-325:13 -/
@[rust_loop]
def decode.stages.Execution.deflate_loop0_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (locator : Slice Std.U64) (quotient : Slice Std.U64) (root : Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, quotient1) => decode.stages.Execution.deflate_loop0_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst locator root iter1
      quotient1)
    (iter, quotient)

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::deflate]: loop body 0:
    Source: 'src/decode/stages.rs', lines 321:8-333:5 -/
@[rust_loop_body]
def decode.stages.Execution.deflate_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (split_at_mut_back : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (index_mut_back : Slice Std.U64 → Slice Std.U64) (r : decode.roots.Roots)
  (s : Slice Std.U64) (s1 : Slice Std.U64) (s2 : Slice Std.U64)
  (s3 : Slice Std.U64) (s4 : Slice Std.U64) (s5 : Slice Std.U64)
  (s6 : Slice types.RawProduct) (s7 : Slice decode.scratch.FactorFrame)
  (sb : decode.scratch.SplitterBasis) (iter : core.slice.iter.Iter Std.U64)
  (locator : Slice Std.U64) (quotient : Slice Std.U64) (degree : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × Std.Usize) ((core.result.Result (Option types.Stage)
    types.DecodeFailure) × decode.roots.Roots × decode.scratch.RowWorkspace
    × (decode.scratch.RowWorkspace → ((Slice Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice types.RawProduct) × (Slice
    decode.scratch.FactorFrame) × decode.scratch.SplitterBasis))))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none =>
    let rest := index_mut_back quotient
    let s8 := split_at_mut_back (locator, rest)
    let (s9, r1, workspace, start_back) ←
      decode.roots.Roots.start r degree
        {
          syndromes := s,
          bm := s8,
          polynomials := s1,
          factors := s2,
          square_table := s3,
          verification := s4,
          roots := s5,
          raw := s6,
          stack := s7,
          basis := sb
        }
    ok (done (core.result.Result.Ok (some s9), r1, workspace,
      fun rw => ((start_back rw).syndromes, (start_back rw).bm,
        (start_back rw).polynomials, (start_back rw).factors,
        (start_back rw).square_table, (start_back rw).verification,
        (start_back rw).roots, (start_back rw).raw, (start_back rw).stack,
        (start_back rw).basis)))
  | some root =>
    let i ← Slice.index_usize locator degree
    let i1 ← degree - 1#usize
    let s8 ← Slice.update quotient i1 i
    let iter2 ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator
        core.iter.range.StepUsize) { start := 1#usize, «end» := degree }
    let quotient1 ←
      decode.stages.Execution.deflate_loop0_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst iter2 locator s8 root
    let i2 ← Slice.index_usize locator 0#usize
    let i3 ← Slice.index_usize quotient1 0#usize
    let i4 ← backendcontractBulkKernelsInst.ArithmeticInst.mul root i3
    let i5 ← lift (i2 ^^^ i4)
    if i5 != 0#u64
    then
      let rest := index_mut_back quotient1
      let s9 := split_at_mut_back (locator, rest)
      ok (done (core.result.Result.Err types.DecodeFailure.InvalidLocator, r,
        {
          syndromes := s,
          bm := s9,
          polynomials := s1,
          factors := s2,
          square_table := s3,
          verification := s4,
          roots := s5,
          raw := s6,
          stack := s7,
          basis := sb
        },
        fun rw =>
          let s10 := rw.syndromes
          let s11 := rw.bm
          let s12 := rw.polynomials
          let s13 := rw.factors
          let s14 := rw.square_table
          let s15 := rw.verification
          let s16 := rw.roots
          let s17 := rw.raw
          let s18 := rw.stack
          let sb1 := rw.basis
          (s10, s11, s12, s13, s14, s15, s16, s17, s18, sb1)))
    else
      let (s9, index_mut_back1) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) locator
          { «end» := degree }
      let s10 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) quotient1
          { «end» := degree }
      let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s9 s10
      let degree1 ← degree - 1#usize
      let locator1 := index_mut_back1 s11
      ok (cont (iter1, locator1, quotient1, degree1))

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::deflate]: loop 0:
    Source: 'src/decode/stages.rs', lines 321:8-333:5 -/
@[rust_loop]
def decode.stages.Execution.deflate_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (split_at_mut_back : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (index_mut_back : Slice Std.U64 → Slice Std.U64)
  (iter : core.slice.iter.Iter Std.U64) (r : decode.roots.Roots)
  (s : Slice Std.U64) (s1 : Slice Std.U64) (s2 : Slice Std.U64)
  (s3 : Slice Std.U64) (s4 : Slice Std.U64) (s5 : Slice Std.U64)
  (s6 : Slice types.RawProduct) (s7 : Slice decode.scratch.FactorFrame)
  (sb : decode.scratch.SplitterBasis) (locator : Slice Std.U64)
  (quotient : Slice Std.U64) (degree : Std.Usize) :
  Result ((core.result.Result (Option types.Stage) types.DecodeFailure) ×
    decode.roots.Roots × decode.scratch.RowWorkspace ×
    (decode.scratch.RowWorkspace → ((Slice Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice types.RawProduct) × (Slice
    decode.scratch.FactorFrame) × decode.scratch.SplitterBasis)))
  := do
  loop
    (fun (iter1, locator1, quotient1, degree1) =>
      decode.stages.Execution.deflate_loop0.body fieldBinaryFieldInst
      backendcontractBulkKernelsInst split_at_mut_back index_mut_back r s s1 s2
      s3 s4 s5 s6 s7 sb iter1 locator1 quotient1 degree1)
    (iter, locator, quotient, degree)

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::deflate]:
    Source: 'src/decode/stages.rs', lines 304:4-333:5 -/
def decode.stages.Execution.deflate
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
  let (r, meter1) ←
    decode.stages.Execution.charge fieldBinaryFieldInst
      backendcontractBulkKernelsInst meter (decode.work.Charge.Deflate
      self.degree)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let width ← capacity + 1#usize
    let ((locator, rest), split_at_mut_back) ←
      core.slice.Slice.split_at_mut workspace.bm width
    let (quotient, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
        { «end» := width }
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) workspace.roots
        { «end» := self.hits }
    let iter ←
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s
    let (r1, r2, workspace1, back) ←
      decode.stages.Execution.deflate_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst split_at_mut_back index_mut_back iter
        self.roots workspace.syndromes workspace.polynomials workspace.factors
        workspace.square_table workspace.verification workspace.roots
        workspace.raw workspace.stack workspace.basis locator quotient
        self.degree
    let back1 :=
      fun workspace2 =>
        let (s1, s2, s3, s4, s5, s6, s7, s8, s9, sb) := back workspace2
        ({
           syndromes := s1,
           bm := s2,
           polynomials := s3,
           factors := s4,
           square_table := s5,
           verification := s6,
           roots := s7,
           raw := s8,
           stack := s9,
           basis := sb
         } : decode.scratch.RowWorkspace)
    ok (core.result.Result.Ok r1, { self with roots := r2 }, workspace1, back1,
      meter1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (core.result.Result (Option types.Stage) types.DecodeFailure)
        (core.convert.FromSame types.DecodeError) residual
    ok (r1, self, workspace, fun workspace1 => workspace1, meter1)

end bulksketch
