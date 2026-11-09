import BulksketchBridge.RankedExecutionDrain

namespace BulksketchBridge.ExecutionFinish

open Aeneas.Std ExecutionDriverRuntime ExecutionDriver
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (run_next finish)

set_option maxRecDepth 4096

/-- An exact nonterminal segment of original successful driver calls.
The explicit workspace continuation composes in source order. -/
inductive SuccessfulChunk (runtime : DrainRuntime) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F) (input : RowInput) :
    Nat → DrainState F K → DrainState F K → (RowWorkspace → RowWorkspace) → Prop
  | empty (before : DrainState F K) : SuccessfulChunk runtime field kernels input 0 before before id
  | step (before middle after : DrainState F K) (stage : Stage) (progress : RowProgress)
      (headBack tailBack : RowWorkspace → RowWorkspace) (length : Nat)
      (running : before.execution.state = .Running stage)
      (source : run_next runtime.calls runtime.division runtime.canonicalize field kernels
        before.execution input before.workspace before.meter =
        .ok (.Ok progress, middle.execution, middle.workspace, headBack, middle.meter))
      (tail : SuccessfulChunk runtime field kernels input length middle after tailBack) :
      SuccessfulChunk runtime field kernels input (length + 1) before after (headBack ∘ tailBack)

theorem chunk_prepend_drain {runtime : DrainRuntime} {F K : Type}
    {field : bulksketch.field.BinaryField F} {kernels : BulkKernels K F} {input : RowInput}
    {used : Nat} {before after : DrainState F K} {back : RowWorkspace → RowWorkspace}
    (segment : SuccessfulChunk runtime field kernels input used before after back)
    {remaining : Nat} {last : Exit F K}
    (rest : DrainTrace runtime field kernels input remaining after.execution after.workspace after.meter last) :
    DrainTrace runtime field kernels input (remaining + used) before.execution before.workspace before.meter
      { last with back := back ∘ last.back } := by
  induction segment with
  | empty => exact rest
  | step before middle after stage progress headBack tailBack length running source tail ih =>
    have step := (run_next_refines runtime.calls runtime.division runtime.canonicalize field kernels
      before.execution input before.workspace before.meter).symm.trans source
    have joined := DrainTrace.continued before.execution before.workspace before.meter stage progress
      middle.execution middle.workspace headBack middle.meter (remaining + length) _ running step (ih rest)
    simpa only [Nat.add_assoc, Function.comp_assoc] using joined

/-- A local source stage can supply one terminal trace or a bounded
successful segment. This admits the exact two-call Trace/GCD and
AffineSplit/GCD handoffs with one rank decrease across both original calls. -/
def RankedChunkLaw (runtime : DrainRuntime) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F) (input : RowInput)
    (maximum : Nat) (admitted : DrainState F K → Prop) (rank : DrainState F K → Nat) : Prop :=
  ∀ (before : DrainState F K) (stage : Stage),
    admitted before → before.execution.state = .Running stage →
    (∃ steps ≤ maximum, ∃ last : Exit F K,
      DrainTrace runtime field kernels input steps before.execution before.workspace before.meter last) ∨
    (∃ steps ≤ maximum, ∃ (after : DrainState F K) (back : RowWorkspace → RowWorkspace),
      SuccessfulChunk runtime field kernels input steps before after back ∧ admitted after ∧ rank after < rank before)

theorem drain_of_ranked_chunks (runtime : DrainRuntime) {F K : Type}
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F) (input : RowInput)
    (maximum : Nat) (admitted : DrainState F K → Prop) (rank : DrainState F K → Nat)
    (driver : RankedChunkLaw runtime field kernels input maximum admitted rank)
    (initial : DrainState F K) (safe : admitted initial) :
    ∃ steps ≤ (rank initial + 1) * maximum, ∃ last : Exit F K,
      DrainTrace runtime field kernels input steps initial.execution initial.workspace initial.meter last := by
  suffices ∀ fuel before, rank before = fuel → admitted before →
      ∃ steps ≤ (fuel + 1) * maximum, ∃ last : Exit F K,
        DrainTrace runtime field kernels input steps before.execution before.workspace before.meter last from
    this (rank initial) initial rfl safe
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro before exactRank safe
    cases selected : stageOption before.execution.state with
    | none => exact ⟨0, Nat.zero_le _, _, .terminal before.execution before.workspace before.meter selected⟩
    | some stage =>
      have running : before.execution.state = .Running stage := by
        cases state : before.execution.state <;> simp_all [stageOption]
      rcases driver before stage safe running with
        ⟨steps, bound, last, trace⟩ | ⟨used, within, after, back, segment, afterSafe, smaller⟩
      · have envelope : maximum ≤ (fuel + 1) * maximum := by
          simpa only [Nat.one_mul] using Nat.mul_le_mul_right maximum (show 1 ≤ fuel + 1 by omega)
        exact ⟨steps, bound.trans envelope, last, trace⟩
      · obtain ⟨remaining, bound, last, trace⟩ := ih (rank after) (by omega) after rfl afterSafe
        have total : remaining + used ≤ (fuel + 1) * maximum := calc
          _ ≤ (rank after + 1) * maximum + maximum := Nat.add_le_add bound within
          _ = (rank after + 2) * maximum := by
            change (rank after + 1) * maximum + maximum = (rank after + 1 + 1) * maximum
            simp only [Nat.add_mul, Nat.one_mul]
          _ ≤ _ := Nat.mul_le_mul_right maximum (by omega)
        exact ⟨remaining + used, total, _, chunk_prepend_drain segment trace⟩

/-- Bounded successful segments construct the exact original finish
trace and its resulting row view, error, meter and callback. -/
def ActualNativeFinishFromRankedChunks : Prop :=
  ∀ (runtime : DrainRuntime) {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (input : RowInput) (maximum : Nat)
    (admitted : DrainState F K → Prop) (rank : DrainState F K → Nat)
    (before : DrainState F K),
    RankedChunkLaw runtime field kernels input maximum admitted rank → admitted before →
    ∃ steps ≤ (rank before + 1) * maximum, ∃ last : Exit F K,
      DrainTrace runtime field kernels input steps before.execution before.workspace before.meter last ∧
      stageOption last.execution.state = none ∧
      finish runtime.calls runtime.division runtime.canonicalize field kernels
        before.execution input before.workspace before.meter = modeled last

theorem native_finish_from_ranked_chunks : ActualNativeFinishFromRankedChunks := by
  intro runtime F K field kernels input maximum admitted rank before law ready
  obtain ⟨steps, bound, last, trace⟩ := drain_of_ranked_chunks runtime field kernels input maximum admitted rank law before ready
  exact ⟨steps, bound, last, trace, (drain_trace_terminal trace).1,
    native_finish runtime.calls runtime.division runtime.canonicalize field kernels before.execution input
      before.workspace before.meter ((rank before + 1) * maximum) last ⟨steps, bound, trace⟩⟩

#print axioms native_finish_from_ranked_chunks

end BulksketchBridge.ExecutionFinish
