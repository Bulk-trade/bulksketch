import BulksketchBridge.NativeExecutionFinish

namespace BulksketchBridge.ExecutionFinish

open Aeneas Aeneas.Std Result ExecutionDriver
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (run_next finish)

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure DrainState (F K : Type) where
  execution : Execution F K
  workspace : RowWorkspace
  meter : WorkMeter

/-- One exact source transition. A successful running successor retains
admission and strictly lowers the rank. A successful terminal step and a
Rust error need no continuation invariant. -/
def RankedDriverStep (runtime : DrainRuntime) {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (input : RowInput)
    (admitted : DrainState F K → Prop) (rank : DrainState F K → Nat) (before : DrainState F K) : Prop :=
  ∃ (reply : core.result.Result RowProgress DecodeError) (after : DrainState F K)
    (back : RowWorkspace → RowWorkspace),
    run_next runtime.calls runtime.division runtime.canonicalize field kernels
      before.execution input before.workspace before.meter =
      .ok (reply, after.execution, after.workspace, back, after.meter) ∧
    match reply with
    | .Err _ => True
    | .Ok _ =>
      stageOption after.execution.state = none ∨ admitted after ∧ rank after < rank before

/-- Source-specific proofs supply the step from every admitted running state. -/
def RankedDriverLaw (runtime : DrainRuntime) {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (input : RowInput)
    (admitted : DrainState F K → Prop) (rank : DrainState F K → Nat) : Prop :=
  ∀ (before : DrainState F K) (stage : Stage),
    admitted before → before.execution.state = .Running stage →
    RankedDriverStep runtime field kernels input admitted rank before

/-- The original run_next error is latched in its returned execution. The
proof uses the actual native transition, so the local ranking law needs
only supply the original Rust result and its exact frame. -/
theorem expected_run_next_latches_error (runtime : DrainRuntime) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F) (input : RowInput)
    (before after : DrainState F K) (stage : Stage) (error : DecodeError)
    (back : RowWorkspace → RowWorkspace) (running : before.execution.state = .Running stage)
    (ran : expectedRunNext runtime.calls runtime.division runtime.canonicalize field kernels
      before.execution input before.workspace before.meter =
      .ok (.Err error, after.execution, after.workspace, back, after.meter)) :
    after.execution.state = .Error error := by
  rw [expectedRunNext, running] at ran
  dsimp only at ran
  cases lower : Execution.execute runtime.calls runtime.division runtime.canonicalize field kernels
      before.execution stage input before.workspace before.meter using Result.cases with
  | ret frame =>
    rw [lower, bind_ok] at ran
    have same := Result.ok_injective ran
    rcases frame with ⟨reply, next, workspace, callback, meter⟩
    cases reply with
    | Err reason =>
      have exactError := congrArg Prod.fst same
      have exactState := congrArg (fun returned : RunFrame F K => returned.2.1.state) same
      change core.result.Result.Err reason = core.result.Result.Err error at exactError
      change State.Error reason = after.execution.state at exactState
      cases exactError
      exact exactState.symm
    | Ok answer =>
      cases answer with
      | Err reason => cases (congrArg Prod.fst same)
      | Ok next => cases next <;> cases (congrArg Prod.fst same)
  | vis effect continuation =>
    rw [lower, bind_vis] at ran
    exact (Aeneas.Std.vis_not_ok ran).elim
  | div =>
    rw [lower, bind_div] at ran
    exact (Aeneas.Std.div_not_ok ran).elim

/-- Strictly smaller ranks construct a finite source trace. Its upper bound
allows one final paid step even when the running state's rank is zero. -/
theorem drain_trace_of_ranked_driver (runtime : DrainRuntime) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F) (input : RowInput)
    (admitted : DrainState F K → Prop) (rank : DrainState F K → Nat)
    (driver : RankedDriverLaw runtime field kernels input admitted rank)
    (initial : DrainState F K) (safe : admitted initial) :
    ∃ steps ≤ rank initial + 1, ∃ last : Exit F K,
      DrainTrace runtime field kernels input steps initial.execution initial.workspace initial.meter last := by
  suffices ∀ fuel (before : DrainState F K), rank before = fuel → admitted before →
      ∃ steps ≤ fuel + 1, ∃ last : Exit F K,
        DrainTrace runtime field kernels input steps before.execution before.workspace before.meter last by
    exact this _ initial rfl safe
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro before rankValue safe
    cases selected : stageOption before.execution.state with
    | none =>
      exact ⟨0, Nat.zero_le _, _, .terminal before.execution before.workspace before.meter selected⟩
    | some stage =>
      have running : before.execution.state = .Running stage := by
        cases state : before.execution.state <;> simp_all [stageOption]
      obtain ⟨reply, after, back, actual, next⟩ := driver before stage safe running
      have step := (run_next_refines runtime.calls runtime.division runtime.canonicalize field kernels
        before.execution input before.workspace before.meter).symm.trans actual
      cases reply with
      | Err error =>
        exact ⟨1, by omega, _, .failed before.execution before.workspace before.meter stage error
          after.execution after.workspace back after.meter running step⟩
      | Ok progress =>
        rcases next with terminal | ⟨afterSafe, smaller⟩
        · have tail : DrainTrace runtime field kernels input 0 after.execution after.workspace after.meter
              ⟨after.execution, after.workspace, after.meter, none, id⟩ :=
            .terminal after.execution after.workspace after.meter terminal
          exact ⟨1, by omega, _, .continued before.execution before.workspace before.meter stage progress
            after.execution after.workspace back after.meter 0 _ running step tail⟩
        · obtain ⟨remaining, bounded, last, tail⟩ := ih (rank after) (by omega) after rfl afterSafe
          exact ⟨remaining + 1, by omega, _, .continued before.execution before.workspace before.meter stage
            progress after.execution after.workspace back after.meter remaining last running step tail⟩

theorem drain_trace_terminal {runtime : DrainRuntime} {F K : Type} {field : bulksketch.field.BinaryField F}
    {kernels : BulkKernels K F} {input : RowInput} {steps : Nat} {self : Execution F K}
    {workspace : RowWorkspace} {meter : WorkMeter} {last : Exit F K}
    (trace : DrainTrace runtime field kernels input steps self workspace meter last) :
    stageOption last.execution.state = none ∧
      (∀ error, last.error = some error → last.execution.state = .Error error) := by
  induction trace with
  | terminal self workspace meter terminal =>
    exact ⟨terminal, by simp⟩
  | failed self workspace meter stage error after written back paid running ran =>
    have latched := expected_run_next_latches_error runtime field kernels input
      ⟨self, workspace, meter⟩ ⟨after, written, paid⟩ stage error back running ran
    change after.state = .Error error at latched
    exact ⟨by simp [latched, stageOption], by simpa only [Option.some.injEq] using
      (fun candidate (same : error = candidate) => same ▸ latched)⟩
  | continued _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ih

/-- Callbacks appear in source execution order. The earliest call is the
outermost application, so the final workspace is propagated backward. -/
theorem drain_trace_callback_order {runtime : DrainRuntime} {F K : Type} {field : bulksketch.field.BinaryField F}
    {kernels : BulkKernels K F} {input : RowInput} {steps : Nat} {self : Execution F K}
    {workspace : RowWorkspace} {meter : WorkMeter} {last : Exit F K}
    (trace : DrainTrace runtime field kernels input steps self workspace meter last) :
    ∃ callbacks : List (RowWorkspace → RowWorkspace), callbacks.length = steps ∧
      last.back = callbacks.foldr (· ∘ ·) id := by
  induction trace with
  | terminal _ _ _ _ => exact ⟨[], rfl, rfl⟩
  | failed _ _ _ _ _ _ _ back _ _ _ => exact ⟨[back], rfl, rfl⟩
  | continued _ _ _ _ _ _ _ back _ _ _ _ _ _ ih =>
    obtain ⟨callbacks, length, order⟩ := ih
    refine ⟨back :: callbacks, by simp [length], ?_⟩
    simpa only [List.foldr_cons] using congrArg (fun tail => back ∘ tail) order

def ActualRankedNativeFinish : Prop :=
  ∀ (runtime : DrainRuntime) {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (input : RowInput) (admitted : DrainState F K → Prop)
    (rank : DrainState F K → Nat) (initial : DrainState F K),
    RankedDriverLaw runtime field kernels input admitted rank → admitted initial →
    ∃ steps ≤ rank initial + 1, ∃ (last : Exit F K) (callbacks : List (RowWorkspace → RowWorkspace)),
      DrainTrace runtime field kernels input steps initial.execution initial.workspace initial.meter last ∧
      stageOption last.execution.state = none ∧
      (∀ error, last.error = some error → last.execution.state = .Error error) ∧
      callbacks.length = steps ∧ last.back = callbacks.foldr (· ∘ ·) id ∧
      finish runtime.calls runtime.division runtime.canonicalize field kernels
        initial.execution input initial.workspace initial.meter = modeled last

theorem ranked_native_finish : ActualRankedNativeFinish := by
  intro runtime F K field kernels input admitted rank initial driver safe
  obtain ⟨steps, bounded, last, trace⟩ :=
    drain_trace_of_ranked_driver runtime field kernels input admitted rank driver initial safe
  obtain ⟨terminal, latched⟩ := drain_trace_terminal trace
  obtain ⟨callbacks, length, order⟩ := drain_trace_callback_order trace
  exact ⟨steps, bounded, last, callbacks, trace, terminal, latched, length, order,
    native_finish runtime.calls runtime.division runtime.canonicalize field kernels
      initial.execution input initial.workspace initial.meter (rank initial + 1) last ⟨steps, bounded, trace⟩⟩

#print axioms expected_run_next_latches_error
#print axioms drain_trace_of_ranked_driver
#print axioms drain_trace_callback_order
#print axioms ranked_native_finish

end BulksketchBridge.ExecutionFinish
