import BulksketchBridge.NativeRootChunks
import BulksketchBridge.RootTraceDivideHandoff
import BulksketchBridge.RootTraceGcdPair
import BulksketchBridge.RootTraceCharge

namespace BulksketchBridge.ExecutionFinish

open Aeneas.Std ExecutionDriver
open bulksketch.decode.scratch bulksketch.decode.row bulksketch.backend.contract bulksketch.types

theorem append_successful_chunks {runtime : DrainRuntime} {F K : Type}
    {field : bulksketch.field.BinaryField F} {kernels : BulkKernels K F} {input : RowInput}
    {m n : Nat} {before middle after : DrainState F K}
    {leftBack rightBack : RowWorkspace → RowWorkspace}
    (left : SuccessfulChunk runtime field kernels input m before middle leftBack)
    (right : SuccessfulChunk runtime field kernels input n middle after rightBack) :
    SuccessfulChunk runtime field kernels input (m + n) before after (leftBack ∘ rightBack) := by
  induction left with
  | empty => simpa only [Nat.zero_add, Function.id_comp] using right
  | step before next middle stage progress headBack restBack length running source rest ih =>
    have joined := SuccessfulChunk.step before next after stage progress headBack (restBack ∘ rightBack)
      (length + n) running source (ih right)
    simpa only [show length + n + 1 = length + 1 + n by omega, Function.comp_assoc] using joined

end BulksketchBridge.ExecutionFinish

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 DenseCoefficient SliceKernels RootTrace RootWorkBudget
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open ExecutionDriver ExecutionDriverRuntime ExecutionFinish
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.stages bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

structure TraceSearchReady {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (point : RootDrainState K) (capacity budget : Nat) : Prop where
  state : point.execution.state = .Running .Trace
  noProbe : point.execution.degree_probe = none
  invariant : RootTraversalInvariant locator point.execution.roots point.workspace capacity budget
  minimum : 3 ≤ point.execution.roots.degree.val
  nonAffine : point.execution.roots.affine = false
  attemptRoom : point.execution.roots.attempts.val + (64 - point.execution.roots.direction.val) ≤ Usize.max
  cache : cacheWellFormed point.execution.roots (buffersFor point.execution.roots point.workspace)
  table : CorrectTable (buffersFor point.execution.roots point.workspace).modulus
    (buffersFor point.execution.roots point.workspace).table point.execution.roots.degree.val
  square : BackendSquareLaw kernels (buffersFor point.execution.roots point.workspace).modulus
    (buffersFor point.execution.roots point.workspace).table point.execution.roots.degree.val
  history : TraceAgreement (activeFactor point.execution.roots point.workspace)
    point.execution.roots.splitter_seed point.execution.roots.direction.val
  live : point.meter.exhausted = false
  available : point.meter.used.val +
    traceSearchUnits point.execution.roots.degree.val point.execution.roots.direction.val
      point.execution.roots.checked ≤ point.meter.limit.val

structure TraceDivisionReady {K : Type} (locator : Polynomial Field)
    (point : RootDrainState K) (capacity budget : Nat) : Prop where
  state : point.execution.state = .Running .FactorDivision
  noProbe : point.execution.degree_probe = none
  invariant : RootTraversalInvariant locator point.execution.roots point.workspace capacity budget
  nonAffine : point.execution.roots.affine = false
  frame : let buffers := buffersFor point.execution.roots point.workspace
    RootDivide.ProperGcdFrame point.execution.roots buffers
      (slicePolynomial (prefixSlice buffers.trace point.execution.roots.trace_len.val))
  history : TraceAgreement (activeFactor point.execution.roots point.workspace)
    point.execution.roots.splitter_seed point.execution.roots.direction.val
  classified : let buffers := buffersFor point.execution.roots point.workspace
    let trace := slicePolynomial (prefixSlice buffers.trace point.execution.roots.trace_len.val)
    ∀ value, (activeFactor point.execution.roots point.workspace).IsRoot value →
      (trace.IsRoot value ↔ traceBit point.execution.roots.splitter_seed
        point.execution.roots.direction.val value = 0)

def ActualNativeTraceSearch : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    ∀ (locator : Polynomial Field) (input : RowInput) (capacity budget : Nat) (before : RootDrainState K),
      budget ≤ 65535 → TraceSearchReady kernels locator before capacity budget →
      ∃ tries after,
        0 < tries ∧ tries ≤ 64 - before.execution.roots.direction.val ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          (2 * tries) before after id ∧
        TraceDivisionReady locator after capacity budget ∧
        after.execution.roots.degree = before.execution.roots.degree ∧
        after.execution.roots.direction.val + 1 = before.execution.roots.direction.val + tries ∧
        after.execution.roots.attempts.val = before.execution.roots.attempts.val + tries ∧
        after.meter.exhausted = false ∧ after.meter.limit = before.meter.limit ∧
        after.meter.used.val = before.meter.used.val +
          tries * (traceUnits before.execution.roots.degree.val + gcdUnits before.execution.roots.degree.val) +
          (if before.execution.roots.checked then 0 else splitCheckUnits before.execution.roots.degree.val)

theorem native_trace_search : ActualNativeTraceSearch := by
  intro canonicalize K kernels raw square reduce mul inverse scale locator input capacity budget initial
    budgetBound initialReady
  suffices ∀ fuel (before : RootDrainState K), fuel = 64 - before.execution.roots.direction.val →
      TraceSearchReady kernels locator before capacity budget →
      ∃ tries after, 0 < tries ∧ tries ≤ fuel ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          (2 * tries) before after id ∧
        TraceDivisionReady locator after capacity budget ∧
        after.execution.roots.degree = before.execution.roots.degree ∧
        after.execution.roots.direction.val + 1 = before.execution.roots.direction.val + tries ∧
        after.execution.roots.attempts.val = before.execution.roots.attempts.val + tries ∧
        after.meter.exhausted = false ∧ after.meter.limit = before.meter.limit ∧
        after.meter.used.val = before.meter.used.val +
          tries * (traceUnits before.execution.roots.degree.val + gcdUnits before.execution.roots.degree.val) +
          (if before.execution.roots.checked then 0 else splitCheckUnits before.execution.roots.degree.val)
    from this _ initial rfl initialReady
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro before exactFuel ready
    let roots := before.execution.roots
    have degreeBound := (traversal_degree_budget locator roots before.workspace capacity budget ready.invariant).trans budgetBound
    have minimum : 3 ≤ roots.degree.val := ready.minimum
    have positive : 0 < before.execution.roots.degree.val := by
      change 0 < roots.degree.val
      omega
    have valid : ValidFactor (activeFactor roots before.workspace) roots.degree.val :=
      ready.invariant.active positive
    have direction : roots.direction.val < 64 := trace_agreement_before_end (activeFactor roots before.workspace)
      roots.splitter_seed roots.direction.val valid.monic.ne_zero valid.split valid.simple
      (by rw [valid.exactDegree]; omega) ready.history
    have fuelEq : fuel = 64 - roots.direction.val := exactFuel
    have attemptsBound : roots.attempts.val + (64 - roots.direction.val) ≤ Usize.max := ready.attemptRoom
    have attempt : roots.attempts.val + 1 ≤ Usize.max := by omega
    have reserve : before.meter.used.val + traceSearchUnits roots.degree.val roots.direction.val roots.checked
        ≤ before.meter.limit.val := ready.available
    rw [trace_search_units_step _ _ _ direction] at reserve
    obtain ⟨paid, traced, final, paidTrace, paidCheck, paidGcd, _, _, used, _, _, limit, _, _, live⟩ :=
      native_trace_attempt_charges roots before.meter degreeBound ready.live (by omega)
    obtain ⟨tracedRoots, afterRoots, tracedWorkspace, written, next, ranTrace, ranGcd, invariant,
      _, _, nonAffine, _, sameDegree, attempts, checked, _, _, table, cache, squareLaw, outcome⟩ :=
      native_trace_gcd_division_ready kernels locator roots before.workspace before.meter paid traced final
        capacity budget ready.invariant minimum ready.nonAffine attempt paidTrace paidCheck paidGcd
        raw square reduce mul inverse scale ready.cache ready.table ready.square ready.history
    let middle := advanceRootState before .Gcd tracedRoots tracedWorkspace traced
    let after := advanceRootState middle next afterRoots written final
    have pair : SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
        2 before after id := native_root_pair_chunk canonicalize kernels before input .Trace .Gcd next
          tracedRoots afterRoots tracedWorkspace written traced final ready.state ready.noProbe rfl rfl ranTrace ranGcd
    rcases outcome with ⟨proper, sameDirection, frame, history, classified⟩ | ⟨retry, stepDirection, history⟩
    · refine ⟨1, after, by decide, by omega, pair,
        ⟨by change State.Running next = _; rw [proper], ready.noProbe, invariant,
          nonAffine, frame, history, classified⟩, sameDegree, ?_, attempts, live, limit, ?_⟩
      · change afterRoots.direction.val + 1 = roots.direction.val + 1
        rw [sameDirection]
      · change final.used.val = before.meter.used.val + 1 * (traceUnits roots.degree.val + gcdUnits roots.degree.val) +
          (if roots.checked then 0 else splitCheckUnits roots.degree.val)
        rw [used, Nat.one_mul]
        omega
    · have smaller : 64 - afterRoots.direction.val < fuel := by omega
      have nextReady : TraceSearchReady kernels locator after capacity budget := by
        refine ⟨by change State.Running next = _; rw [retry], ready.noProbe, invariant,
          by change 3 ≤ afterRoots.degree.val; rw [sameDegree]; exact minimum, nonAffine,
          ?_, cache, table, squareLaw, history, live, ?_⟩
        · change afterRoots.attempts.val + (64 - afterRoots.direction.val) ≤ Usize.max
          omega
        · change final.used.val + traceSearchUnits afterRoots.degree.val afterRoots.direction.val afterRoots.checked
            ≤ final.limit.val
          rw [used, limit, sameDegree, stepDirection, checked]
          omega
      obtain ⟨more, done, positiveMore, bounded, segment, readyDone, exactDegree, exactDirection,
        exactAttempts, doneLive, doneLimit, doneUsed⟩ := ih (64 - afterRoots.direction.val) smaller after rfl nextReady
      refine ⟨more + 1, done, by omega, by omega, ?_, readyDone, exactDegree.trans sameDegree, ?_, ?_,
        doneLive, doneLimit.trans limit, ?_⟩
      · have joined := append_successful_chunks pair segment
        simpa only [Function.id_comp, Nat.mul_add, Nat.mul_one, Nat.add_comm] using joined
      · change done.execution.roots.direction.val + 1 = roots.direction.val + (more + 1)
        change done.execution.roots.direction.val + 1 = afterRoots.direction.val + more at exactDirection
        omega
      · change done.execution.roots.attempts.val = roots.attempts.val + (more + 1)
        change done.execution.roots.attempts.val = afterRoots.attempts.val + more at exactAttempts
        omega
      · change done.meter.used.val =
          before.meter.used.val + (more + 1) * (traceUnits roots.degree.val + gcdUnits roots.degree.val) +
            (if roots.checked then 0 else splitCheckUnits roots.degree.val)
        change done.meter.used.val =
          final.used.val + more * (traceUnits afterRoots.degree.val + gcdUnits afterRoots.degree.val) +
            (if afterRoots.checked then 0 else splitCheckUnits afterRoots.degree.val) at doneUsed
        rw [doneUsed, used, sameDegree, checked, Nat.add_mul, Nat.one_mul]
        simp only [ite_true, Nat.add_zero]
        omega

#print axioms native_trace_search

end BulksketchBridge.RootRun
