import BulksketchBridge.NativeTraceFrontier
import BulksketchBridge.NativeNonaffineReducerReady
import BulksketchBridge.NativeTraceNode

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 DenseCoefficient SliceKernels RootTrace RootWorkBudget
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open ExecutionDriver ExecutionDriverRuntime ExecutionFinish ClosedLeafAdvance
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.stages bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 5500000

/-- The paid native reducer, trace search and split spend exactly from
the active frontier slot and leave both children and all earlier
siblings admitted, with a smaller traversal potential. -/
def ActualNativeTraceFrontierSplit : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    TimesXMod.ExactScaleXor kernels →
    (∀ (modulus table : Slice U64) (degree : Nat),
      CorrectTable modulus table degree → BackendSquareLaw kernels modulus table degree) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels →
    ∀ (locator : Polynomial Field) (input : RowInput) (before : RootDrainState K) (capacity budget : Nat),
      budget ≤ 65535 → NativeTraceFrontier locator before capacity budget →
      before.execution.state = .Running .ReducerPreparation → 3 ≤ before.execution.roots.degree.val →
      ∃ (tries : Nat) (after : RootDrainState K),
        tries ≤ 64 ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          (2 * tries + 2) before after id ∧
        after.execution.budget = before.execution.budget ∧ after.meter.limit = before.meter.limit ∧
        before.meter.used.val ≤ after.meter.used.val ∧
        NativeTraceFrontier locator after capacity budget ∧
        after.meter.used.val + frontierWork after.execution.roots after.workspace.stack ≤
          before.meter.used.val + frontierWork before.execution.roots before.workspace.stack ∧
        traversalPotential after.execution.roots after.workspace.stack <
          traversalPotential before.execution.roots before.workspace.stack

theorem native_trace_frontier_split : ActualNativeTraceFrontierSplit := by
  intro canonicalize K kernels scale backend raw square reduce mul inverse locator input before capacity budget
    budgetFit ready running minimum
  let roots := before.execution.roots
  let degree := roots.degree.val
  have degreeMin : 3 ≤ degree := minimum
  have envelope : nodeEnvelope degree ≤ rootsEnvelope degree := by
    have fit := roots_envelope_split 1 (degree - 1) degree (by decide) (by omega) degreeMin (by omega)
    omega
  have reserve : before.meter.used.val + (rootsEnvelope degree + _) ≤ before.meter.limit.val :=
    ready.reserve
  have attemptReserve : roots.attempts.val + 64 * ((degree - 1) + _) ≤ Usize.max := ready.attempts
  have attempts : roots.attempts.val + (64 - roots.direction.val) ≤ Usize.max := by omega
  have checks : (if roots.checked then 0 else splitCheckUnits degree) ≤ splitCheckUnits degree := by
    cases roots.checked <;> simp
  have pair := Nat.mul_le_mul_right (traceUnits degree + gcdUnits degree) (Nat.sub_le 64 roots.direction.val)
  have localReserve : tableUnits degree + traceSearchUnits degree roots.direction.val roots.checked +
      divideUnits degree + assemblyUnits degree ≤ nodeEnvelope degree := by
    rw [← node_envelope_expanded, traceSearchUnits]
    omega
  have room : before.meter.used.val + tableUnits degree + traceSearchUnits degree roots.direction.val roots.checked +
      divideUnits degree + assemblyUnits degree ≤ before.meter.limit.val := by omega
  obtain ⟨prepared, prep, prepReady, prepRoots, prepWidths, _, prepUsed, prepLimit, prepStack, prepFactors, prepBudget⟩ :=
    native_nonaffine_reducer_fixed canonicalize kernels scale backend locator input before capacity budget
      running ready.noProbe ready.traversal budgetFit minimum ready.nonAffine attempts ready.cache ready.history ready.live (by
        change before.meter.used.val + tableUnits degree +
          traceSearchUnits degree roots.direction.val roots.checked ≤ before.meter.limit.val
        omega)
  change prepared.meter.used.val = before.meter.used.val + tableUnits degree at prepUsed
  have nextRoom : prepared.meter.used.val + traceSearchUnits prepared.execution.roots.degree.val
      prepared.execution.roots.direction.val prepared.execution.roots.checked +
      divideUnits prepared.execution.roots.degree.val + assemblyUnits prepared.execution.roots.degree.val ≤
        prepared.meter.limit.val := by
    rwa [prepRoots, prepUsed, prepLimit]
  obtain ⟨tries, divider, after, frame, _, bounded, node, _, _, _, next, traversal, read, direction, _,
    history, pendingHistory, live, limit, used, spent, info⟩ :=
      native_trace_node_frame canonicalize kernels raw square reduce mul inverse scale locator input capacity budget
        prepared budgetFit prepReady nextRoom
  have dividerDegree : divider.execution.roots.degree = roots.degree :=
    info.degree.trans (congrArg Roots.degree prepRoots)
  have dividerPending : divider.execution.roots.pending = roots.pending :=
    info.search.fixed.pending.trans (congrArg Roots.pending prepRoots)
  have dividerStride : divider.execution.roots.stride = roots.stride :=
    info.search.fixed.stride.trans (congrArg Roots.stride prepRoots)
  have seed : after.execution.roots.splitter_seed = roots.splitter_seed :=
    info.seed.trans (info.search.seed.trans (congrArg Roots.splitter_seed prepRoots))
  have dividerStack : divider.workspace.stack = before.workspace.stack := info.search.stack.trans prepStack
  have dividerFactors : divider.workspace.factors = before.workspace.factors := info.search.factors.trans prepFactors
  have widths : workspaceLengths after.workspace = workspaceLengths before.workspace :=
    info.split.widths.trans (info.search.fixed.widths.trans prepWidths)
  have count : after.execution.roots.pending.val = roots.pending.val + 1 := by
    rw [info.split.pending, dividerPending]
  have older : ∀ slot < roots.pending.val, after.workspace.stack.val[slot]? = before.workspace.stack.val[slot]? := by
    intro slot present
    rw [← dividerStack]
    exact info.earlierStack slot (dividerPending.symm ▸ present)
  have newest : after.workspace.stack.val[roots.pending.val]? = some frame := by rwa [dividerPending] at read
  have degreeSum : after.execution.roots.degree.val + (frame.coefficient_len.val - 1) = degree := by
    rw [info.split.degreeSum, dividerDegree]
  obtain ⟨workCredit, attemptCredit⟩ := frontier_proper_split roots after.execution.roots
    before.workspace.stack after.workspace.stack frame count older newest
    info.split.leftPositive info.split.rightPositive minimum degreeSum
  rw [prepRoots, prepUsed] at used spent
  change after.meter.used.val = before.meter.used.val + tableUnits degree +
    tries * (traceUnits degree + gcdUnits degree) +
    (if roots.checked then 0 else splitCheckUnits degree) + divideUnits degree + assemblyUnits degree at used
  change after.meter.used.val - (before.meter.used.val + tableUnits degree) + tableUnits degree ≤
    nodeEnvelope degree at spent
  have debit : after.meter.used.val ≤ before.meter.used.val + nodeEnvelope degree := by omega
  have more : before.meter.used.val ≤ after.meter.used.val := by omega
  have limitEq : after.meter.limit = before.meter.limit := limit.trans prepLimit
  have cache : cacheWellFormed after.execution.roots (buffersFor after.execution.roots after.workspace) := by
    have beforeCache := info.search.cache
    unfold cacheWellFormed at beforeCache ⊢
    change ∀ basis, after.workspace.basis.directions = some basis →
      1 ≤ after.workspace.basis.len.val ∧ after.workspace.basis.len.val ≤ 64 ∧
        cachePrefix after.execution.roots.splitter_seed basis after.workspace.basis.len.val
    rw [info.basis, info.seed]
    exact beforeCache
  have attemptBound : tries ≤ 64 := bounded.trans (Nat.sub_le ..)
  have afterAttempts : after.execution.roots.attempts.val = roots.attempts.val + tries := by
    rw [info.split.attempts, info.attempts, prepRoots]
  have start : frame.coefficient_start.val = roots.pending.val * roots.stride.val := by
    rw [info.split.start, dividerPending, dividerStride]
  have earlierWords : ∀ i < roots.pending.val * roots.stride.val,
      after.workspace.factors[i]! = before.workspace.factors[i]! := by
    intro i bounded
    rw [← dividerFactors]
    exact info.earlierWords i (start.symm ▸ bounded)
  have pending : PendingTraceHistory after.execution.roots after.workspace := by
    intro slot saved inRange exactRead
    by_cases isNew : slot = roots.pending.val
    · subst slot
      have same := Option.some.inj (newest.symm.trans exactRead)
      subst saved
      exact pendingHistory
    · have earlier : slot < roots.pending.val := by omega
      have savedRead : before.workspace.stack.val[slot]? = some saved := by rwa [older slot earlier] at exactRead
      obtain ⟨f, read, shape⟩ := ready.traversal.layout.slots slot earlier
      have same := Option.some.inj (read.symm.trans savedRead)
      subst f
      have unchanged := RootDivide.older_pending_factor roots before.workspace after.workspace saved slot earlier shape
        ready.traversal.layout.factorRoom (congrArg WorkspaceAdmission.Lengths.factors widths) earlierWords
      rw [unchanged, seed]
      exact ready.pending slot saved earlier savedRead
  have potential := info.split.potential
  change traversalPotential after.execution.roots after.workspace.stack <
    traversalPotential divider.execution.roots divider.workspace.stack at potential
  rw [dividerStack] at potential
  unfold traversalPotential at potential
  rw [dividerDegree, dividerPending] at potential
  have rank : traversalPotential after.execution.roots after.workspace.stack <
      traversalPotential roots before.workspace.stack := potential
  change nodeEnvelope degree + frontierWork after.execution.roots after.workspace.stack ≤
    frontierWork roots before.workspace.stack at workCredit
  have balance : after.meter.used.val + frontierWork after.execution.roots after.workspace.stack ≤
      before.meter.used.val + frontierWork roots before.workspace.stack := by omega
  have afterReady : NativeTraceFrontier locator after capacity budget := by
    refine ⟨next, info.noProbe, traversal, ?_, info.nonAffine, ?_, history, pending, cache, ?_, live, ?_⟩
    · change WorkspaceAdmission.Admitted (workspaceLengths after.workspace) capacity budget
      rw [widths]
      exact ready.workspace
    · rw [info.split.closedForm, info.search.fixed.closedForm, prepRoots]
      exact ready.plain
    · have initial : roots.attempts.val + 64 * frontierSplits roots before.workspace.stack ≤ Usize.max := ready.attempts
      rw [afterAttempts]
      omega
    · rw [limitEq]
      exact balance.trans ready.reserve
  have joined := append_successful_chunks prep node
  exact ⟨tries, after, attemptBound, by
    simpa only [Function.id_comp, show 1 + (2 * tries + 1) = 2 * tries + 2 by omega] using joined,
    info.budget.trans prepBudget, limitEq, more, afterReady, balance, rank⟩

#print axioms native_trace_frontier_split

end BulksketchBridge.RootRun
