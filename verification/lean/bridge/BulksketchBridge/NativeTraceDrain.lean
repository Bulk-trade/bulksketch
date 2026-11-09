import BulksketchBridge.NativeTraceFrontierSplit

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 RootWorkBudget SliceKernels
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open ExecutionDriver ExecutionDriverRuntime ExecutionFinish ClosedLeafAdvance
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.stages bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 5200000

/-- The original V1/V2 frontier runs to its emitted locator. Each
iteration executes exact source steps and either emits the last factor
or preserves the work balance and decreases the traversal potential. -/
def ActualNativeTraceDrain : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    TimesXMod.ExactScaleXor kernels →
    (∀ (modulus table : Slice U64) (degree : Nat),
      CorrectTable modulus table degree → BackendSquareLaw kernels modulus table degree) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels → DirectTwo.CorrectArithmetic kernels →
    ∀ (locator : Polynomial Field) (input : RowInput) (before : RootDrainState K) (capacity budget : Nat),
      budget ≤ 65535 → NativeTraceFrontier locator before capacity budget →
      ∃ (steps : Nat) (after : RootDrainState K),
        steps ≤ 130 * (traversalPotential before.execution.roots before.workspace.stack + 1) ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          steps before after id ∧
        NativeTraceEmitted locator after capacity budget ∧
        after.execution.budget = before.execution.budget ∧ after.meter.limit = before.meter.limit ∧
        before.meter.used.val ≤ after.meter.used.val ∧
        after.meter.used.val ≤ before.meter.used.val + frontierWork before.execution.roots before.workspace.stack

theorem native_trace_drain : ActualNativeTraceDrain := by
  intro canonicalize K kernels scale backend raw square reduce mul inverse arithmetic locator input initial capacity budget
    budgetFit ready
  suffices ∀ n (before : RootDrainState K),
      traversalPotential before.execution.roots before.workspace.stack = n →
      NativeTraceFrontier locator before capacity budget →
      ∃ (steps : Nat) (after : RootDrainState K), steps ≤ 130 * (n + 1) ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          steps before after id ∧
        NativeTraceEmitted locator after capacity budget ∧
        after.execution.budget = before.execution.budget ∧ after.meter.limit = before.meter.limit ∧
        before.meter.used.val ≤ after.meter.used.val ∧
        after.meter.used.val ≤ before.meter.used.val + frontierWork before.execution.roots before.workspace.stack
    from this _ initial rfl ready
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro before rank ready
    have prepend (cost : Nat) (next : RootDrainState K) (size : cost ≤ 130)
        (chunk : SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          cost before next id)
        (sameBudget : next.execution.budget = before.execution.budget)
        (sameLimit : next.meter.limit = before.meter.limit)
        (more : before.meter.used.val ≤ next.meter.used.val)
        (safe : NativeTraceFrontier locator next capacity budget)
        (remaining : next.meter.used.val + frontierWork next.execution.roots next.workspace.stack ≤
          before.meter.used.val + frontierWork before.execution.roots before.workspace.stack)
        (smaller : traversalPotential next.execution.roots next.workspace.stack <
          traversalPotential before.execution.roots before.workspace.stack) :
        ∃ (steps : Nat) (after : RootDrainState K), steps ≤ 130 * (n + 1) ∧
          SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
            steps before after id ∧ NativeTraceEmitted locator after capacity budget ∧
          after.execution.budget = before.execution.budget ∧ after.meter.limit = before.meter.limit ∧
          before.meter.used.val ≤ after.meter.used.val ∧
          after.meter.used.val ≤ before.meter.used.val + frontierWork before.execution.roots before.workspace.stack := by
      rw [rank] at smaller
      obtain ⟨tail, after, bound, suffix, emitted, budget, limit, grows, debit⟩ := ih _ smaller next rfl safe
      refine ⟨cost + tail, after, by omega, ?_, emitted, budget.trans sameBudget, limit.trans sameLimit,
        more.trans grows, debit.trans remaining⟩
      simpa only [Function.id_comp] using append_successful_chunks chunk suffix
    by_cases small : before.execution.roots.degree < 3#usize
    · have running : before.execution.state = .Running .Leaf := by
        simpa only [stageFor, small, ite_true] using ready.state
      have bounded : before.execution.roots.degree.val ≤ 2 := by
        change before.execution.roots.degree.val < 3 at small
        omega
      obtain ⟨after, step, budget, limit, more, debit, outcome⟩ :=
        native_trace_frontier_leaf canonicalize kernels arithmetic locator input before capacity budget ready running bounded
      rcases outcome with emitted | ⟨safe, remaining, smaller⟩
      · exact ⟨1, after, by omega, step, emitted, budget, limit, more, debit⟩
      · exact prepend 1 after (by decide) step budget limit more safe remaining smaller
    · have running : before.execution.state = .Running .ReducerPreparation := by
        simpa only [stageFor, small, ready.plain, ite_false, Bool.false_eq_true, false_and] using ready.state
      have minimum : 3 ≤ before.execution.roots.degree.val := by
        change ¬ before.execution.roots.degree.val < 3 at small
        omega
      obtain ⟨tries, after, bound, step, budget, limit, more, safe, remaining, smaller⟩ :=
        native_trace_frontier_split canonicalize kernels scale backend raw square reduce mul inverse locator input before
          capacity budget budgetFit ready running minimum
      exact prepend (2 * tries + 2) after (by omega) step budget limit more safe remaining smaller

#print axioms native_trace_drain

end BulksketchBridge.RootRun
