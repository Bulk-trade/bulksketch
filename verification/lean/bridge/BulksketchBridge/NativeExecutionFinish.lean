import Arithmetic.FinishGenerated
import BulksketchBridge.ExecutionDriver
import BulksketchBridge.NativeCompletedResult
import BulksketchBridge.NativeDeflate

namespace BulksketchBridge.ExecutionFinish

open Aeneas Aeneas.Std Result ExecutionDriverRuntime ExecutionDriver
open Deflation (WorkspaceParts workspaceParts workspaceFromParts workspace_round_trip)
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution
  (finish finish_loop)

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure Exit (F K : Type) where
  execution : Execution F K
  workspace : RowWorkspace
  meter : WorkMeter
  error : Option DecodeError
  back : RowWorkspace → RowWorkspace

structure DrainRuntime where
  calls : RootRunRuntime.OtherCallees
  division : DenseDivisionRuntime.DivRem
  canonicalize : Canonicalize

/-- A finite, exact sequence of admitted source transitions. Successful
steps continue. The original Rust error result stops immediately and the
normal exit is observed only when the original stage is terminal. -/
inductive DrainTrace (runtime : DrainRuntime) {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (input : RowInput) :
    Nat → Execution F K → RowWorkspace → WorkMeter → Exit F K → Prop
  | terminal (self : Execution F K) (workspace : RowWorkspace) (meter : WorkMeter)
      (done : stageOption self.state = none) :
      DrainTrace runtime field kernels input 0 self workspace meter
        ⟨self, workspace, meter, none, id⟩
  | failed (self : Execution F K) (workspace : RowWorkspace) (meter : WorkMeter)
      (stage : Stage) (error : DecodeError) (after : Execution F K) (written : RowWorkspace)
      (back : RowWorkspace → RowWorkspace) (paid : WorkMeter)
      (running : self.state = .Running stage)
      (step : expectedRunNext runtime.calls runtime.division runtime.canonicalize field kernels self input workspace meter =
        .ok (.Err error, after, written, back, paid)) :
      DrainTrace runtime field kernels input 1 self workspace meter
        ⟨after, written, paid, some error, back⟩
  | continued (self : Execution F K) (workspace : RowWorkspace) (meter : WorkMeter)
      (stage : Stage) (progress : RowProgress) (after : Execution F K) (written : RowWorkspace)
      (back : RowWorkspace → RowWorkspace) (paid : WorkMeter) (remaining : Nat) (last : Exit F K)
      (running : self.state = .Running stage)
      (step : expectedRunNext runtime.calls runtime.division runtime.canonicalize field kernels self input workspace meter =
        .ok (.Ok progress, after, written, back, paid))
      (rest : DrainTrace runtime field kernels input remaining after written paid last) :
      DrainTrace runtime field kernels input (remaining + 1) self workspace meter
        { last with back := back ∘ last.back }

abbrev LoopBack := RowWorkspace → WorkspaceParts
abbrev LoopExit (F K : Type) :=
  Execution F K × RowWorkspace × WorkMeter × Bool × core.result.Result Never DecodeError × LoopBack

def encoded {F K : Type} (last : Exit F K) (back : LoopBack) : LoopExit F K :=
  (last.execution, last.workspace, last.meter, last.error.isNone,
    .Err (last.error.getD .WorkLimitExceeded), back ∘ last.back)

private theorem finish_once (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem)
    (canonicalize : Canonicalize) {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (input : RowInput) (back : LoopBack)
    (self : Execution F K) (workspace : RowWorkspace) (meter : WorkMeter) :
    finish_loop calls division canonicalize field kernels back self input.difference input.candidates workspace meter =
    (do
      let step ← finish_loop.body calls division canonicalize field kernels
        input.difference input.candidates back self workspace meter
      match step with
      | .done output => .ok output
      | .cont (nextBack, next, written, paid) =>
        finish_loop calls division canonicalize field kernels nextBack next input.difference input.candidates
          written paid) := by
  rw [finish_loop, loop]
  dsimp! only
  congr 1
  funext step
  cases step with
  | done output => rfl
  | cont state => rcases state with ⟨nextBack, next, written, paid⟩; rfl

theorem finish_loop_from_trace
    {runtime : DrainRuntime} {F K : Type} {field : bulksketch.field.BinaryField F} {kernels : BulkKernels K F}
    {input : RowInput} {steps : Nat} {self : Execution F K} {workspace : RowWorkspace}
    {meter : WorkMeter} {last : Exit F K}
    (trace : DrainTrace runtime field kernels input steps self workspace meter last)
    (back : LoopBack) :
    finish_loop runtime.calls runtime.division runtime.canonicalize field kernels back self input.difference input.candidates workspace meter =
      .ok (encoded last back) := by
  induction trace generalizing back with
  | terminal self workspace meter terminal =>
    rw [finish_once, finish_loop.body, next_stage_refines, terminal]
    simp only [bind_ok, core.option.Option.is_some, Option.isSome, Bool.false_eq_true, ite_false]
    rfl
  | failed self workspace meter stage error after written returned paid running step =>
    rw [finish_once, finish_loop.body, next_stage_refines, running, stageOption]
    simp only [bind_ok, core.option.Option.is_some, Option.isSome, eq_self, ite_true]
    rw [run_next_refines, step]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    dsimp! only
    rw [bind_ok]
    dsimp! only
    rw [bind_ok]
    rfl
  | continued self workspace meter stage progress after written returned paid remaining last running step _ ih =>
    rw [finish_once, finish_loop.body, next_stage_refines, running, stageOption]
    simp only [bind_ok, core.option.Option.is_some, Option.isSome, eq_self, ite_true]
    rw [run_next_refines, step]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    dsimp! only
    rw [bind_ok]
    dsimp! only
    rw [bind_ok]
    exact ih (back ∘ returned)

def modeled {F K : Type} (last : Exit F K) :
    Result (core.result.Result RowResult DecodeError × RowWorkspace ×
      (RowWorkspace → RowWorkspace) × WorkMeter) := do
  let reply ← match last.error with
    | none => CompletedResult.outcome last.execution last.workspace
    | some error => .ok (.Err error)
  .ok (reply, last.workspace, last.back, last.meter)

/-- The checked source wrapper implements bounded draining with the
original residual and the ordered composition of workspace callbacks. -/
def ActualNativeFinish : Prop :=
  ∀ (calls : RootRunRuntime.OtherCallees) (division : DenseDivisionRuntime.DivRem) (canonicalize : Canonicalize)
    {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Execution F K) (input : RowInput) (workspace : RowWorkspace) (meter : WorkMeter)
    (bound : Nat) (last : Exit F K),
    (∃ steps ≤ bound, DrainTrace ⟨calls, division, canonicalize⟩ field kernels input steps self workspace meter last) →
    finish calls division canonicalize field kernels self input workspace meter = modeled last

theorem native_finish : ActualNativeFinish := by
  intro calls division canonicalize F K field kernels self input workspace meter bound last certificate
  obtain ⟨steps, _, trace⟩ := certificate
  have drained : finish_loop calls division canonicalize field kernels workspaceParts self input.difference
      input.candidates workspace meter = .ok (encoded last workspaceParts) :=
    finish_loop_from_trace trace workspaceParts
  unfold finish
  change (do
    let (next, written, paid, normal, residual, back) ←
      finish_loop calls division canonicalize field kernels workspaceParts self input.difference
        input.candidates workspace meter
    if normal then
      let reply ← Execution.completed_result field kernels next written
      .ok (reply, written, fun w => workspaceFromParts (back w), paid)
    else
      let reply ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual RowResult
        (core.convert.FromSame DecodeError) residual
      .ok (reply, written, fun w => workspaceFromParts (back w), paid)) = _
  rw [drained]
  simp only [bind_tc_ok]
  have restored : (fun w => workspaceFromParts (workspaceParts (last.back w))) = last.back :=
    funext (fun w => workspace_round_trip (last.back w))
  cases outcome : last.error with
  | none =>
    simp only [encoded, modeled, Function.comp_def, outcome, Option.isNone, Option.getD,
      eq_self, ite_true, restored]
    rw [CompletedResult.native_completed_result field kernels last.execution last.workspace]
    rfl
  | some reason =>
    simp only [encoded, modeled, Function.comp_def, outcome, Option.isNone, Option.getD,
      Bool.false_eq_true, ite_false, bind_ok, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      restored]

#print axioms finish_loop_from_trace
#print axioms native_finish

end BulksketchBridge.ExecutionFinish
