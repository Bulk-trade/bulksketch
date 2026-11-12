-- Checked original declarations after guarded slice lowering from original Execution::canonicalize.
import Arithmetic.ExecutionDriverGenerated
import BulksketchBridge.CanonicalizeOrdering

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Aeneas.Std.CanonicalizeRuntime

open BulksketchBridge.CanonicalizeOrdering

abbrev SortWords := core.cmp.Ord U64 → Slice U64 → Result (Slice U64)

def pairSlice (left right : U64) : Slice U64 :=
  Slice.from [left, right] (by scalar_tac)

def scan {T C : Type} (callback : core.ops.function.FnMut C T Bool) :
    List T → C → Result (Bool × Nat)
  | [], _ => .ok (false, 0)
  | item :: rest, state => do
    let (found, state') ← callback.call_mut state item
    if found then .ok (true, 1) else
      let (later, consumed) ← scan callback rest state'
      .ok (later, consumed + 1)

def anyShared {C : Type} (callback : core.ops.function.FnMut C U64 Bool)
    (it : core.slice.iter.Iter U64) (state : C) :
    Result (Bool × core.slice.iter.Iter U64) := do
  let (found, consumed) ← scan callback (it.slice.val.drop it.i) state
  .ok (found, { it with i := it.i + consumed })

def windows (words : Slice U64) (width : Usize) : Result (List (Slice U64)) :=
  if width = 2#usize then .ok ((pairWindows words.val).map fun pair => pairSlice pair.1 pair.2)
  else .fail .panic

def anyWindows {C : Type} (_ : Unit) (callback : core.ops.function.FnMut C (Slice U64) Bool)
    (it : List (Slice U64)) (state : C) : Result (Bool × List (Slice U64)) := do
  let (found, consumed) ← scan callback it state
  .ok (found, it.drop consumed)

end Aeneas.Std.CanonicalizeRuntime

namespace bulksketch

variable (sortModel : CanonicalizeRuntime.SortWords)
local notation "core.slice.Slice.sort_unstable" => sortModel
local notation "core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any" =>
  CanonicalizeRuntime.anyShared
local notation "core.slice.Slice.windows" => CanonicalizeRuntime.windows
local notation "core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice" => (fun (_ : Type) => ())
local notation "core.iter.traits.iterator.Iterator.any.default" => CanonicalizeRuntime.anyWindows

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{closure#1}]
    Source: 'src/decode/stages.rs', lines 400:36-400:61 -/
@[reducible]
def decode.stages.Execution.canonicalize.closure_1 (F : Type _) (K : Type _) :=
Unit

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{closure}]
    Source: 'src/decode/stages.rs', lines 399:28-399:69 -/
@[reducible]
def decode.stages.Execution.canonicalize.closure (F : Type _) (K : Type _) :=
Unit

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{impl core::ops::function::FnMut<(&'_0 [u64],), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{closure#1}<'_0, F, K>}::call_mut]:
    Source: 'src/decode/stages.rs', lines 400:36-400:61 -/
def
  decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool.call_mut
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.stages.Execution.canonicalize.closure_1 F K)
  (tupled_args : Slice Std.U64) :
  Result (Bool × (decode.stages.Execution.canonicalize.closure_1 F K))
  := do
  let i ← Slice.index_usize tupled_args 0#usize
  let i1 ← Slice.index_usize tupled_args 1#usize
  ok (i = i1, ())

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{impl core::ops::function::FnOnce<(&'_0 [u64],), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{closure#1}<'_0, F, K>}::call_once]:
    Source: 'src/decode/stages.rs', lines 400:36-400:61 -/
def
  decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU64Bool.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.stages.Execution.canonicalize.closure_1 F K) (s : Slice Std.U64)
  :
  Result Bool
  := do
  let (b, _) ←
    decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool.call_mut
      fieldBinaryFieldInst backendcontractBulkKernelsInst () s
  ok b

/-- Trait implementation: [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{impl core::ops::function::FnOnce<(&'_0 [u64],), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{closure#1}<'_0, F, K>}]
    Source: 'src/decode/stages.rs', lines 400:36-400:61 -/
@[reducible]
def
  decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.stages.Execution.canonicalize.closure_1 F K)
  (Slice Std.U64) Bool := {
  call_once :=
    decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU64Bool.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- Trait implementation: [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{impl core::ops::function::FnMut<(&'_0 [u64],), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{closure#1}<'_0, F, K>}]
    Source: 'src/decode/stages.rs', lines 400:36-400:61 -/
@[reducible]
def
  decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnMut (decode.stages.Execution.canonicalize.closure_1 F K)
  (Slice Std.U64) Bool := {
  FnOnceInst :=
    decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU64Bool
    fieldBinaryFieldInst backendcontractBulkKernelsInst
  call_mut :=
    decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool.call_mut
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{impl core::ops::function::FnMut<(&'_0 u64,), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{closure}<'_0, F, K>}::call_mut]:
    Source: 'src/decode/stages.rs', lines 399:28-399:69 -/
def
  decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.stages.Execution.canonicalize.closure F K)
  (tupled_args : Std.U64) :
  Result (Bool × (decode.stages.Execution.canonicalize.closure F K))
  := do
  if tupled_args = 0#u64
  then ok (true, ())
  else
    let i ← fieldBinaryFieldInst.MASK
    let i1 ← lift (~~~ i)
    let i2 ← lift (tupled_args &&& i1)
    ok (i2 != 0#u64, ())

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{impl core::ops::function::FnOnce<(&'_0 u64,), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{closure}<'_0, F, K>}::call_once]:
    Source: 'src/decode/stages.rs', lines 399:28-399:69 -/
def
  decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.stages.Execution.canonicalize.closure F K) (i : Std.U64) :
  Result Bool
  := do
  let (b, _) ←
    decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
      fieldBinaryFieldInst backendcontractBulkKernelsInst () i
  ok b

/-- Trait implementation: [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{impl core::ops::function::FnOnce<(&'_0 u64,), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{closure}<'_0, F, K>}]
    Source: 'src/decode/stages.rs', lines 399:28-399:69 -/
@[reducible]
def
  decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.stages.Execution.canonicalize.closure F K)
  Std.U64 Bool := {
  call_once :=
    decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- Trait implementation: [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{impl core::ops::function::FnMut<(&'_0 u64,), bool> for bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize::{closure}<'_0, F, K>}]
    Source: 'src/decode/stages.rs', lines 399:28-399:69 -/
@[reducible]
def
  decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnMut (decode.stages.Execution.canonicalize.closure F K)
  Std.U64 Bool := {
  FnOnceInst :=
    decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool
    fieldBinaryFieldInst backendcontractBulkKernelsInst
  call_mut :=
    decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::canonicalize]:
    Source: 'src/decode/stages.rs', lines 373:4-405:5 -/
def decode.stages.Execution.canonicalize
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K)
  (workspace : decode.scratch.RowWorkspace) (meter : types.WorkMeter) :
  Result ((core.result.Result (core.result.Result (Option types.Stage)
    types.DecodeFailure) types.DecodeError) × (decode.stages.Execution F K) ×
    decode.scratch.RowWorkspace × (decode.scratch.RowWorkspace →
    decode.scratch.RowWorkspace) × types.WorkMeter)
  := do
  let (r, meter1) ←
    decode.stages.Execution.charge fieldBinaryFieldInst
      backendcontractBulkKernelsInst meter (decode.work.Charge.Canonicalize
      self.budget.total)
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    if self.roots.count > self.budget.nonzero
    then
      ok (core.result.Result.Ok (core.result.Result.Err
        types.DecodeFailure.DegreeExceedsBudget), self, workspace,
        fun workspace1 => workspace1, meter1)
    else
      let (roots, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64)
          workspace.roots { «end» := self.roots.count }
      let i := Slice.len roots
      let (meter2, roots1) ←
        if i = 2#usize
        then
          do
          let ((s, s1), split_at_mut_back) ←
            core.slice.Slice.split_at_mut roots 1#usize
          let (left, index_mut_back1) ← Slice.index_mut_usize s 0#usize
          let (right, index_mut_back2) ← Slice.index_mut_usize s1 0#usize
          let (i1, i2) ←
            if left > right
            then ok (core.mem.swap left right)
            else ok (left, right)
          let s2 := index_mut_back2 i2
          let s3 := index_mut_back1 i1
          let s4 := split_at_mut_back (s3, s2)
          ok (meter1, s4)
        else
          let i1 := Slice.len roots
          if i1 = 0#usize
          then ok (meter1, roots)
          else
            do
            let i2 := Slice.len roots
            let s ←
              if i2 = 1#usize
              then ok roots
              else core.slice.Slice.sort_unstable core.cmp.OrdU64 roots
            ok (meter1, s)
      let i1 ← core.slice.Slice.iter roots1
      let (b, _) ←
        core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
          (decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool
          fieldBinaryFieldInst backendcontractBulkKernelsInst) i1 ()
      if b
      then
        let s := index_mut_back roots1
        ok (core.result.Result.Ok (core.result.Result.Err
          types.DecodeFailure.InvalidLocator), self,
          { workspace with roots := s }, fun workspace1 => workspace1, meter2)
      else
        let w ← core.slice.Slice.windows roots1 2#usize
        let (b1, _) ←
          core.iter.traits.iterator.Iterator.any.default
            (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
            Std.U64)
            (decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool
            fieldBinaryFieldInst backendcontractBulkKernelsInst) w ()
        if b1
        then
          let s := index_mut_back roots1
          ok (core.result.Result.Ok (core.result.Result.Err
            types.DecodeFailure.InvalidLocator), self,
            { workspace with roots := s }, fun workspace1 => workspace1,
            meter2)
        else
          let s := index_mut_back roots1
          ok (core.result.Result.Ok (core.result.Result.Ok none), self,
            { workspace with roots := s }, fun workspace1 => workspace1,
            meter2)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        (core.result.Result (Option types.Stage) types.DecodeFailure)
        (core.convert.FromSame types.DecodeError) residual
    ok (r1, self, workspace, fun workspace1 => workspace1, meter1)

end bulksketch
