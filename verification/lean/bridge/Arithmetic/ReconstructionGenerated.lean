-- Exact declarations projected from the original reconstruction extraction.
import Arithmetic.ReconstructionRuntime
import Arithmetic.ReconstructionWorkspace
import Arithmetic.WorkScheduleGenerated
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
namespace bulksketch

local notation "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all" => Aeneas.Std.ReconstructionRuntime.sliceAll
local notation "decode.stages.check_workspace" => BulksketchBridge.Reconstruction.checkWorkspace

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct::{impl core::ops::function::FnMut<(&'_0 u64,), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct::{closure}<'_0, F, K>}::call_mut]:
    Source: 'src/decode/stages.rs', lines 249:43-249:62 -/
def
  decode.stages.Execution.reconstruct.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.stages.Execution.reconstruct.closure F K) (tupled_args : Std.U64)
  :
  Result (Bool × (decode.stages.Execution.reconstruct.closure F K))
  := do
  ok (tupled_args = 0#u64, ())

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct::{impl core::ops::function::FnOnce<(&'_0 u64,), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct::{closure}<'_0, F, K>}::call_once]:
    Source: 'src/decode/stages.rs', lines 249:43-249:62 -/
def
  decode.stages.Execution.reconstruct.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.stages.Execution.reconstruct.closure F K) (i : Std.U64) :
  Result Bool
  := do
  let (b, _) ←
    decode.stages.Execution.reconstruct.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
      fieldBinaryFieldInst backendcontractBulkKernelsInst () i
  ok b

/-- Trait implementation: [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct::{impl core::ops::function::FnOnce<(&'_0 u64,), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct::{closure}<'_0, F, K>}]
    Source: 'src/decode/stages.rs', lines 249:43-249:62 -/
@[reducible]
def
  decode.stages.Execution.reconstruct.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.stages.Execution.reconstruct.closure F K)
  Std.U64 Bool := {
  call_once :=
    decode.stages.Execution.reconstruct.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- Trait implementation: [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct::{impl core::ops::function::FnMut<(&'_0 u64,), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct::{closure}<'_0, F, K>}]
    Source: 'src/decode/stages.rs', lines 249:43-249:62 -/
@[reducible]
def
  decode.stages.Execution.reconstruct.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnMut (decode.stages.Execution.reconstruct.closure F K)
  Std.U64 Bool := {
  FnOnceInst :=
    decode.stages.Execution.reconstruct.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool
    fieldBinaryFieldInst backendcontractBulkKernelsInst
  call_mut :=
    decode.stages.Execution.reconstruct.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct]: loop body 0:
    Source: 'src/decode/stages.rs', lines 257:8-263:9 -/
@[rust_loop_body]
def decode.stages.Execution.reconstruct_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (s : Slice Std.U64) (iter : core.ops.range.RangeInclusive Std.Usize)
  (s1 : Slice Std.U64) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) × (Slice
    Std.U64)) (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done s1)
  | some i =>
    let b ← core.num.Usize.is_multiple_of i 2#usize
    let i1 ←
      if b
      then
        do
        let i2 ← i / 2#usize
        let i3 ← Slice.index_usize s1 i2
        backendcontractBulkKernelsInst.ArithmeticInst.square i3
      else do
           let i2 ← i / 2#usize
           Slice.index_usize s i2
    let s2 ← Slice.update s1 i i1
    ok (cont (iter1, s2))

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct]: loop 0:
    Source: 'src/decode/stages.rs', lines 257:8-263:9 -/
@[rust_loop]
def decode.stages.Execution.reconstruct_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.RangeInclusive Std.Usize) (s : Slice Std.U64)
  (s1 : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, s2) => decode.stages.Execution.reconstruct_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst s iter1 s2)
    (iter, s1)

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct]: loop body 1:
    Source: 'src/decode/stages.rs', lines 257:8-263:9 -/
@[rust_loop_body]
def decode.stages.Execution.reconstruct_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (s : Slice Std.U64) (iter : core.ops.range.RangeInclusive Std.Usize)
  (s1 : Slice Std.U64) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) × (Slice
    Std.U64)) (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok (done s1)
  | some i =>
    let b ← core.num.Usize.is_multiple_of i 2#usize
    let i1 ←
      if b
      then
        do
        let i2 ← i / 2#usize
        let i3 ← Slice.index_usize s1 i2
        backendcontractBulkKernelsInst.ArithmeticInst.square i3
      else do
           let i2 ← i / 2#usize
           Slice.index_usize s i2
    let s2 ← Slice.update s1 i i1
    ok (cont (iter1, s2))

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct]: loop 1:
    Source: 'src/decode/stages.rs', lines 257:8-263:9 -/
@[rust_loop]
def decode.stages.Execution.reconstruct_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.RangeInclusive Std.Usize) (s : Slice Std.U64)
  (s1 : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, s2) => decode.stages.Execution.reconstruct_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst s iter1 s2)
    (iter, s1)

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::reconstruct]:
    Source: 'src/decode/stages.rs', lines 241:4-265:5 -/
def decode.stages.Execution.reconstruct
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
  if self.budget.total = self.budget.nonzero
  then
    let i ← core.slice.Slice.iter input.difference
    let (b, _) ←
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
        (decode.stages.Execution.reconstruct.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool
        fieldBinaryFieldInst backendcontractBulkKernelsInst) i ()
    if b
    then
      let (r, meter1) ← types.WorkMeter.charge meter 0#u64
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        ok (core.result.Result.Ok (core.result.Result.Ok none), self,
          workspace, fun workspace1 => workspace1, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r1, self, workspace, fun workspace1 => workspace1, meter1)
    else
      let (r, meter1) ←
        decode.stages.Execution.charge fieldBinaryFieldInst
          backendcontractBulkKernelsInst meter (decode.work.Charge.Reconstruct
          capacity)
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r1 ←
          decode.stages.check_workspace workspace capacity self.budget.nonzero
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let s ← Slice.update workspace.syndromes 0#usize 0#u64
          let i1 ← 2#usize * capacity
          let iter ← core.ops.range.RangeInclusive.new 1#usize i1
          let s1 ←
            decode.stages.Execution.reconstruct_loop0 fieldBinaryFieldInst
              backendcontractBulkKernelsInst iter input.difference s
          ok (core.result.Result.Ok (core.result.Result.Ok (some
            types.Stage.BerlekampMassey)), self,
            { workspace with syndromes := s1 }, fun workspace1 => workspace1,
            meter1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (core.result.Result (Option types.Stage) types.DecodeFailure)
              (core.convert.FromSame types.DecodeError) residual
          ok (r2, self, workspace, fun workspace1 => workspace1, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r1, self, workspace, fun workspace1 => workspace1, meter1)
  else
    let (r, meter1) ←
      decode.stages.Execution.charge fieldBinaryFieldInst
        backendcontractBulkKernelsInst meter (decode.work.Charge.Reconstruct
        capacity)
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ←
        decode.stages.check_workspace workspace capacity self.budget.nonzero
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s ← Slice.update workspace.syndromes 0#usize 0#u64
        let i ← 2#usize * capacity
        let iter ← core.ops.range.RangeInclusive.new 1#usize i
        let s1 ←
          decode.stages.Execution.reconstruct_loop1 fieldBinaryFieldInst
            backendcontractBulkKernelsInst iter input.difference s
        ok (core.result.Result.Ok (core.result.Result.Ok (some
          types.Stage.BerlekampMassey)), self,
          { workspace with syndromes := s1 }, fun workspace1 => workspace1,
          meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, self, workspace, fun workspace1 => workspace1, meter1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (core.result.Result (Option types.Stage) types.DecodeFailure)
          (core.convert.FromSame types.DecodeError) residual
      ok (r1, self, workspace, fun workspace1 => workspace1, meter1)

end bulksketch
