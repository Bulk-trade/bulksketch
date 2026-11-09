-- Checked original finish projection with a scoped shared-return boundary.
import Arithmetic.ExecutionDriverGenerated
import Arithmetic.CompletedResultGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
open Aeneas.Std.ExecutionDriverRuntime
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace bulksketch

variable (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
variable (canonicalizeModel : Canonicalize)

local notation "decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next" => (decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next calls division canonicalizeModel)

/-- [bulksketch::decode::stages::{impl bulksketch::decode::row::RowExecution for bulksketch::decode::stages::Execution<F, K>}::finish]: loop body 0:
    Source: 'src/decode/stages.rs', lines 448:8-452:5 -/
@[rust_loop_body]
def
  decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.finish_loop.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (s : Slice Std.U64) (s1 : Slice Std.U64)
  (back : decode.scratch.RowWorkspace → ((Slice Std.U64) × (Slice Std.U64)
  × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64)
  × (Slice Std.U64) × (Slice types.RawProduct) × (Slice
  decode.scratch.FactorFrame) × decode.scratch.SplitterBasis))
  (self : decode.stages.Execution F K)
  (workspace : decode.scratch.RowWorkspace) (meter : types.WorkMeter) :
  Result (ControlFlow ((decode.scratch.RowWorkspace → ((Slice Std.U64) ×
    (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice Std.U64) × (Slice types.RawProduct) × (Slice
    decode.scratch.FactorFrame) × decode.scratch.SplitterBasis)) ×
    (decode.stages.Execution F K) × decode.scratch.RowWorkspace ×
    types.WorkMeter) ((decode.stages.Execution F K) ×
    decode.scratch.RowWorkspace × types.WorkMeter × Bool ×
    (core.result.Result Never types.DecodeError) ×
    (decode.scratch.RowWorkspace → ((Slice Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice types.RawProduct) × (Slice
    decode.scratch.FactorFrame) × decode.scratch.SplitterBasis))))
  := do
  let o ←
    decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.next_stage
      fieldBinaryFieldInst backendcontractBulkKernelsInst self
  let b := core.option.Option.is_some o
  if b
  then
    let (r, self1, workspace1, run_next_back, meter1) ←
      decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next
        fieldBinaryFieldInst backendcontractBulkKernelsInst self
        { difference := s, candidates := s1 } workspace meter
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      ok (cont (fun rw => back (run_next_back rw), self1, workspace1, meter1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      ok (done (self1, workspace1, meter1, false, residual,
        fun rw => back (run_next_back rw)))
  else
    ok (done (self, workspace, meter, true, core.result.Result.Err
      types.DecodeError.WorkLimitExceeded,
      fun rw =>
        let s2 := rw.syndromes
        let s3 := rw.bm
        let s4 := rw.polynomials
        let s5 := rw.factors
        let s6 := rw.square_table
        let s7 := rw.verification
        let s8 := rw.roots
        let s9 := rw.raw
        let s10 := rw.stack
        let sb := rw.basis
        back
          {
            syndromes := s2,
            bm := s3,
            polynomials := s4,
            factors := s5,
            square_table := s6,
            verification := s7,
            roots := s8,
            raw := s9,
            stack := s10,
            basis := sb
          }))

local notation "decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.finish_loop.body" => (decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.finish_loop.body calls division canonicalizeModel)

/-- [bulksketch::decode::stages::{impl bulksketch::decode::row::RowExecution for bulksketch::decode::stages::Execution<F, K>}::finish]: loop 0:
    Source: 'src/decode/stages.rs', lines 448:8-452:5 -/
@[rust_loop]
def decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.finish_loop
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (back : decode.scratch.RowWorkspace → ((Slice Std.U64) × (Slice Std.U64)
  × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64)
  × (Slice Std.U64) × (Slice types.RawProduct) × (Slice
  decode.scratch.FactorFrame) × decode.scratch.SplitterBasis))
  (self : decode.stages.Execution F K) (s : Slice Std.U64) (s1 : Slice Std.U64)
  (workspace : decode.scratch.RowWorkspace) (meter : types.WorkMeter) :
  Result ((decode.stages.Execution F K) × decode.scratch.RowWorkspace ×
    types.WorkMeter × Bool × (core.result.Result Never types.DecodeError) ×
    (decode.scratch.RowWorkspace → ((Slice Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice types.RawProduct) × (Slice
    decode.scratch.FactorFrame) × decode.scratch.SplitterBasis)))
  := do
  loop
    (fun (back1, self1, workspace1, meter1) =>
      decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.finish_loop.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst s s1 back1 self1
      workspace1 meter1)
    (back, self, workspace, meter)

local notation "decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.finish_loop" => (decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.finish_loop calls division canonicalizeModel)

/-- [bulksketch::decode::stages::{impl bulksketch::decode::row::RowExecution for bulksketch::decode::stages::Execution<F, K>}::finish]:
    Source: 'src/decode/stages.rs', lines 442:4-452:5 -/
def decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.finish
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) (input : decode.row.RowInput)
  (workspace : decode.scratch.RowWorkspace) (meter : types.WorkMeter) :
  Result ((core.result.Result decode.row.RowResult types.DecodeError) ×
    decode.scratch.RowWorkspace × (decode.scratch.RowWorkspace →
    decode.scratch.RowWorkspace) × types.WorkMeter)
  := do
  let (self1, workspace1, meter1, finish_normal, finish_residual, back) ←
    decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.finish_loop
      fieldBinaryFieldInst backendcontractBulkKernelsInst
      (fun rw =>
        let s := rw.syndromes
        let s1 := rw.bm
        let s2 := rw.polynomials
        let s3 := rw.factors
        let s4 := rw.square_table
        let s5 := rw.verification
        let s6 := rw.roots
        let s7 := rw.raw
        let s8 := rw.stack
        let sb := rw.basis
        (s, s1, s2, s3, s4, s5, s6, s7, s8, sb)) self input.difference
      input.candidates workspace meter
  if finish_normal
  then
    let r ←
      decode.stages.Execution.completed_result fieldBinaryFieldInst
        backendcontractBulkKernelsInst self1 workspace1
    let back1 :=
      fun workspace2 =>
        let (s, s1, s2, s3, s4, s5, s6, s7, s8, sb) := back workspace2
        ({
           syndromes := s,
           bm := s1,
           polynomials := s2,
           factors := s3,
           square_table := s4,
           verification := s5,
           roots := s6,
           raw := s7,
           stack := s8,
           basis := sb
         } : decode.scratch.RowWorkspace)
    ok (r, workspace1, back1, meter1)
  else
    let r ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        decode.row.RowResult (core.convert.FromSame types.DecodeError)
        finish_residual
    let back1 :=
      fun workspace2 =>
        let (s, s1, s2, s3, s4, s5, s6, s7, s8, sb) := back workspace2
        ({
           syndromes := s,
           bm := s1,
           polynomials := s2,
           factors := s3,
           square_table := s4,
           verification := s5,
           roots := s6,
           raw := s7,
           stack := s8,
           basis := sb
         } : decode.scratch.RowWorkspace)
    ok (r, workspace1, back1, meter1)

end bulksketch
