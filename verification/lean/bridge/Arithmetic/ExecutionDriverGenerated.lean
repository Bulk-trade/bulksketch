-- Exact stock checked decoder driver declarations.
import Arithmetic.RootRunGenerated
import Arithmetic.BmLocatorGenerated
import Arithmetic.CandidateOuterGenerated
import Arithmetic.NativeDeflateGenerated
import Arithmetic.ExecutionVerifyGenerated

open Aeneas Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace Aeneas.Std.ExecutionDriverRuntime

open bulksketch.backend.contract bulksketch.decode.stages
open bulksketch.decode.scratch bulksketch.types

abbrev StageReply := core.result.Result (core.result.Result (Option Stage) DecodeFailure) DecodeError
abbrev Frame (F K : Type) :=
  StageReply × Execution F K × RowWorkspace × (RowWorkspace → RowWorkspace) × WorkMeter
abbrev Canonicalize :=
  ∀ {F K : Type}, bulksketch.field.BinaryField F → BulkKernels K F →
    Execution F K → RowWorkspace → WorkMeter → Result (Frame F K)

def optionEq {T : Type} (cmp : core.cmp.PartialEq T T) (left right : Option T) : Result Bool :=
  match left, right with
  | none, none => .ok true
  | some a, some b => cmp.eq a b
  | _, _ => .ok false

def resultMap {T E U F : Type} (callback : core.ops.function.FnOnce F T U)
    (value : core.result.Result T E) (function : F) : Result (core.result.Result U E) :=
  match value with
  | .Err error => .ok (.Err error)
  | .Ok input => do
    let output ← callback.call_once function input
    .ok (.Ok output)

def someValue {T : Type} (value : T) : Result (Option T) := .ok (some value)
def someCall {T : Type} (constructor : T → Result (Option T)) (value : T) : Result (Option T) :=
  constructor value

end Aeneas.Std.ExecutionDriverRuntime

namespace bulksketch

open ExecutionDriverRuntime

local notation "P.Insts.CoreOpsFunctionFnOnceTupleTOption.call_once" => someCall
local notation "core.option.Option.Some.constructor" => someValue
local notation "core.option.Option.Insts.CoreCmpPartialEqOption.eq" => optionEq
local notation "core.result.Result.map" => resultMap

/-- [bulksketch::decode::row::RowProgress]
    Source: 'src/decode/row.rs', lines 38:0-44:1 -/
structure decode.row.RowProgress where
  stage : types.Stage
  locator_degree : Std.Usize
  candidate_hits : Std.Usize
  trace_attempts : Std.Usize
  gcd_degree : Std.Usize

/-- Trait implementation: [core::option::Option::{impl core::ops::function::FnOnce<(T,), core::option::Option<T>> for core::option::Option::Some<T>}]
    Source: '/rustc/library/core/src/option.rs', lines 606:4-606:8
    Name pattern: [core::ops::function::FnOnce<@, (@T), core::option::Option<@T>>] -/
@[reducible, rust_trait_impl
  "core::ops::function::FnOnce<@, (@T), core::option::Option<@T>>"]
def P.Insts.CoreOpsFunctionFnOnceTupleTOption (T : Type _) :
  core.ops.function.FnOnce (T → Result (Option T)) T (Option T) := {
  call_once := P.Insts.CoreOpsFunctionFnOnceTupleTOption.call_once
}

variable (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
variable (canonicalizeModel : Canonicalize)

local notation "decode.roots.Roots.run" => (decode.roots.Roots.run calls division)
local notation "decode.stages.Execution.canonicalize" => canonicalizeModel

/-- [bulksketch::decode::stages::{bulksketch::decode::stages::Execution<F, K>}::execute]:
    Source: 'src/decode/stages.rs', lines 166:4-240:5 -/
def decode.stages.Execution.execute
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) (stage : types.Stage)
  (input : decode.row.RowInput) (workspace : decode.scratch.RowWorkspace)
  (meter : types.WorkMeter) :
  Result ((core.result.Result (core.result.Result (Option types.Stage)
    types.DecodeFailure) types.DecodeError) × (decode.stages.Execution F K) ×
    decode.scratch.RowWorkspace × (decode.scratch.RowWorkspace →
    decode.scratch.RowWorkspace) × types.WorkMeter)
  := do
  let capacity := Slice.len input.difference
  match self.degree_probe with
  | none =>
    match stage with
    | types.Stage.DirectOne =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.DirectOne
          workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.DirectTwo =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.DirectTwo
          workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.GuardThree =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.GuardThree
          workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.NewtonThree =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.NewtonThree
          workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.GuardFour =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.GuardFour
          workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.NewtonFour =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.NewtonFour
          workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.LeafThree =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.LeafThree
          workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.LeafFour =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.LeafFour
          workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.FactorVerification =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots
          types.Stage.FactorVerification workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.Reconstruction =>
      decode.stages.Execution.reconstruct fieldBinaryFieldInst
        backendcontractBulkKernelsInst self input workspace meter
    | types.Stage.BerlekampMassey =>
      let (r, s, meter1) ←
        decode.bm.locator fieldBinaryFieldInst backendcontractBulkKernelsInst
          workspace.syndromes capacity self.budget.nonzero workspace.bm meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        match val with
        | core.result.Result.Ok d =>
          let i ← Slice.index_usize s 0#usize
          if i = 0#u64
          then
            ok (core.result.Result.Ok (core.result.Result.Err
              types.DecodeFailure.InvalidLocator), { self with degree := d },
              { workspace with bm := s }, fun workspace1 => workspace1, meter1)
          else
            ok (core.result.Result.Ok (core.result.Result.Ok (some
              types.Stage.CandidateEvaluation)), { self with degree := d },
              { workspace with bm := s }, fun workspace1 => workspace1, meter1)
        | core.result.Result.Err e =>
          ok (core.result.Result.Ok (core.result.Result.Err e), self,
            { workspace with bm := s }, fun workspace1 => workspace1, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r1, self, { workspace with bm := s }, fun workspace1 => workspace1,
          meter1)
    | types.Stage.CandidateEvaluation =>
      decode.stages.Execution.candidates fieldBinaryFieldInst
        backendcontractBulkKernelsInst self input workspace meter
    | types.Stage.Deflation =>
      decode.stages.Execution.deflate fieldBinaryFieldInst
        backendcontractBulkKernelsInst self input workspace meter
    | types.Stage.ReducerPreparation =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots
          types.Stage.ReducerPreparation workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.AffinePreparation =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots
          types.Stage.AffinePreparation workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.AffineEnumeration =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots
          types.Stage.AffineEnumeration workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.AffineSplit =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.AffineSplit
          workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.Trace =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.Trace workspace
          meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.Gcd =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.Gcd workspace
          meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.FactorDivision =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.FactorDivision
          workspace meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.Leaf =>
      let (r, r1, workspace1, run_back, meter1) ←
        decode.roots.Roots.run fieldBinaryFieldInst
          backendcontractBulkKernelsInst self.roots types.Stage.Leaf workspace
          meter
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let r2 ←
          core.result.Result.map (P.Insts.CoreOpsFunctionFnOnceTupleTOption
            types.Stage) val (core.option.Option.Some.constructor)
        ok (core.result.Result.Ok r2, { self with roots := r1 }, workspace1,
          run_back, meter1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (core.result.Result (Option types.Stage) types.DecodeFailure)
            (core.convert.FromSame types.DecodeError) residual
        ok (r2, { self with roots := r1 }, workspace1, run_back, meter1)
    | types.Stage.Verification =>
      decode.stages.Execution.verify fieldBinaryFieldInst
        backendcontractBulkKernelsInst self input workspace meter
    | types.Stage.Canonicalization =>
      decode.stages.Execution.canonicalize fieldBinaryFieldInst
        backendcontractBulkKernelsInst self workspace meter
  | some probe =>
    let (r, probe1, workspace1, run_back, meter1) ←
      decode.degree_probe.DegreeProbe.run fieldBinaryFieldInst
        backendcontractBulkKernelsInst probe input.difference self.budget
        workspace meter
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let i ← decode.degree_probe.DegreeProbe.impl.count probe1
      let b ←
        core.option.Option.Insts.CoreCmpPartialEqOption.eq
          types.Stage.Insts.CoreCmpPartialEqStage val (some
          types.Stage.Reconstruction)
      if b
      then
        ok (core.result.Result.Ok (core.result.Result.Ok val),
          {
            self
              with
              roots := { self.roots with count := i }, degree_probe := none
          }, workspace1, run_back, meter1)
      else
        ok (core.result.Result.Ok (core.result.Result.Ok val),
          {
            self
              with
              roots := { self.roots with count := i },
              degree_probe := (some probe1)
          }, workspace1, run_back, meter1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (core.result.Result (Option types.Stage) types.DecodeFailure)
          (core.convert.FromSame types.DecodeError) residual
      ok (r1, { self with degree_probe := (some probe1) }, workspace1,
        run_back, meter1)

local notation "decode.stages.Execution.execute" => (decode.stages.Execution.execute calls division canonicalizeModel)

/-- [bulksketch::decode::stages::{impl bulksketch::decode::row::RowExecution for bulksketch::decode::stages::Execution<F, K>}::run_next]:
    Source: 'src/decode/stages.rs', lines 414:4-441:5 -/
def decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.run_next
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) (input : decode.row.RowInput)
  (workspace : decode.scratch.RowWorkspace) (meter : types.WorkMeter) :
  Result ((core.result.Result decode.row.RowProgress types.DecodeError) ×
    (decode.stages.Execution F K) × decode.scratch.RowWorkspace ×
    (decode.scratch.RowWorkspace → decode.scratch.RowWorkspace) ×
    types.WorkMeter)
  := do
  match self.state with
  | decode.stages.State.Running stage =>
    let (r, self1, workspace1, execute_back, meter1) ←
      decode.stages.Execution.execute fieldBinaryFieldInst
        backendcontractBulkKernelsInst self stage input workspace meter
    match r with
    | core.result.Result.Ok r1 =>
      match r1 with
      | core.result.Result.Ok o =>
        match o with
        | none =>
          ok (core.result.Result.Ok
            {
              stage,
              locator_degree := self1.degree,
              candidate_hits := self1.hits,
              trace_attempts := self1.roots.attempts,
              gcd_degree := self1.roots.gcd_degree
            }, { self1 with state := decode.stages.State.Complete },
            workspace1, execute_back, meter1)
        | some next =>
          ok (core.result.Result.Ok
            {
              stage,
              locator_degree := self1.degree,
              candidate_hits := self1.hits,
              trace_attempts := self1.roots.attempts,
              gcd_degree := self1.roots.gcd_degree
            }, { self1 with state := (decode.stages.State.Running next) },
            workspace1, execute_back, meter1)
      | core.result.Result.Err reason =>
        ok (core.result.Result.Ok
          {
            stage,
            locator_degree := self1.degree,
            candidate_hits := self1.hits,
            trace_attempts := self1.roots.attempts,
            gcd_degree := self1.roots.gcd_degree
          }, { self1 with state := (decode.stages.State.Failed reason) },
          workspace1, execute_back, meter1)
    | core.result.Result.Err error =>
      ok (core.result.Result.Err error,
        { self1 with state := (decode.stages.State.Error error) }, workspace1,
        execute_back, meter1)
  | decode.stages.State.Complete => fail panic
  | decode.stages.State.Failed _ => fail panic
  | decode.stages.State.Error error =>
    ok (core.result.Result.Err error, self, workspace,
      fun workspace1 => workspace1, meter)

/-- [bulksketch::decode::stages::{impl bulksketch::decode::row::RowExecution for bulksketch::decode::stages::Execution<F, K>}::next_stage]:
    Source: 'src/decode/stages.rs', lines 408:4-413:5 -/
def decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution.next_stage
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (self : decode.stages.Execution F K) :
  Result (Option types.Stage)
  := do
  match self.state with
  | decode.stages.State.Running stage => ok (some stage)
  | decode.stages.State.Complete => ok none
  | decode.stages.State.Failed _ => ok none
  | decode.stages.State.Error _ => ok none

end bulksketch
