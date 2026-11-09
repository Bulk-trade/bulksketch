import BulksketchBridge.NativeTraceNode
import BulksketchBridge.RootReducerInvariant
import BulksketchBridge.RootTraversalFactor

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 DenseCoefficient RootTrace DenseReducerAlgebra DenseReducerSquare
open ExecutionDriver ExecutionDriverRuntime ExecutionFinish RootWorkBudget
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.stages bulksketch.types

set_option maxRecDepth 4096

/-- The original non-affine reducer entry pays its exact table charge
and restores Trace readiness for the initial factor or a saved child. -/
def ActualNativeNonaffineReducerReady : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    TimesXMod.ExactScaleXor kernels →
    (∀ (modulus table : Slice U64) (degree : Nat),
      CorrectTable modulus table degree → BackendSquareLaw kernels modulus table degree) →
    ∀ (locator : Polynomial Field) (input : RowInput) (before : RootDrainState K) (capacity budget : Nat),
      let roots := before.execution.roots
      before.execution.state = .Running .ReducerPreparation → before.execution.degree_probe = none →
      RootTraversalInvariant locator roots before.workspace capacity budget → budget ≤ 65535 →
      3 ≤ roots.degree.val → roots.affine = false →
      roots.attempts.val + (64 - roots.direction.val) ≤ Usize.max →
      cacheWellFormed roots (buffersFor roots before.workspace) →
      TraceAgreement (activeFactor roots before.workspace) roots.splitter_seed roots.direction.val →
      before.meter.exhausted = false →
      before.meter.used.val + tableUnits roots.degree.val +
        traceSearchUnits roots.degree.val roots.direction.val roots.checked ≤ before.meter.limit.val →
      ∃ after : RootDrainState K,
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input 1 before after id ∧
        TraceSearchReady kernels locator after capacity budget ∧ after.execution.roots = roots ∧
        workspaceLengths after.workspace = workspaceLengths before.workspace ∧
        after.workspace.basis = before.workspace.basis ∧
        after.meter.used.val = before.meter.used.val + tableUnits roots.degree.val ∧
        after.meter.limit = before.meter.limit

theorem native_nonaffine_reducer_ready : ActualNativeNonaffineReducerReady := by
  intro canonicalize K kernels scale square locator input before capacity budget roots state noProbe
    invariant budgetFit degreeMin affine attempt cache agreement live reserve
  have bound := traversal_degree_budget locator roots before.workspace capacity budget invariant
  obtain ⟨⟨amount, price, value⟩, _⟩ := native_root_node_prices roots.degree (bound.trans budgetFit)
  obtain ⟨paid, charged, used, limit, paidLive⟩ := native_roots_paid_charge before.meter (.Table roots.degree)
    amount (tableUnits roots.degree.val) price value live (by omega)
  obtain ⟨written, ran, retained, correct, _⟩ := native_reducer_invariant kernels locator roots before.workspace
    before.meter paid capacity budget invariant degreeMin scale charged
  have monic := traversal_monic_word locator roots before.workspace capacity budget invariant (by omega)
  obtain ⟨table, work, exactRun, exactReborrow, _, widths, sameFactor⟩ := native_reducer_preparation kernels
    roots before.workspace before.meter paid capacity budget invariant.buffers degreeMin bound scale charged monic
  let modeled := rebuild before.workspace roots { buffersFor roots before.workspace with table, work }
  have writtenEq : written = modeled :=
    congrArg (fun frame : Frame => frame.2.2.1) (Result.ok_injective (ran.symm.trans exactRun))
  have sameBasis : written.basis = before.workspace.basis := by rw [writtenEq]; rfl
  have cached : cacheWellFormed roots (buffersFor roots written) := by
    rw [writtenEq, show buffersFor roots modeled = { buffersFor roots before.workspace with table, work }
      from exactReborrow]
    exact cache
  have history : TraceAgreement (activeFactor roots written) roots.splitter_seed roots.direction.val := by
    rw [writtenEq, show activeFactor roots modeled = activeFactor roots before.workspace from sameFactor]
    exact agreement
  have next : tableStage roots = .Trace := by simp [tableStage, affine]
  rw [next] at ran
  let after := advanceRootState before .Trace roots written paid
  have step := native_root_driver_return canonicalize kernels before.execution .ReducerPreparation input before.workspace
    before.meter paid (.Ok (.Ok .Trace)) roots written id state noProbe rfl ran
  have segment : SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
      1 before after id :=
    SuccessfulChunk.step before after after .ReducerPreparation
      (progress .ReducerPreparation { before.execution with roots }) id id 0 state step (.empty after)
  refine ⟨after, segment,
    ⟨rfl, noProbe, retained, degreeMin, affine, attempt, cached, correct, square _ _ _ correct, history, paidLive, ?_⟩,
    rfl, ?_, sameBasis, used, limit⟩
  · change paid.used.val + traceSearchUnits roots.degree.val roots.direction.val roots.checked ≤ paid.limit.val
    rwa [used, limit]
  · change workspaceLengths written = _
    rw [writtenEq]
    exact widths

/-- One complete native non-affine node fits the original envelope
from its first reducer call through both paid division charges. -/
def ActualNativeNonaffineReducerNode : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    TimesXMod.ExactScaleXor kernels →
    (∀ (modulus table : Slice U64) (degree : Nat),
      CorrectTable modulus table degree → BackendSquareLaw kernels modulus table degree) →
    DenseMulConvolutionSpec.RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels →
    ∀ (locator : Polynomial Field) (input : RowInput) (before : RootDrainState K) (capacity budget : Nat),
      let roots := before.execution.roots
      before.execution.state = .Running .ReducerPreparation → before.execution.degree_probe = none →
      RootTraversalInvariant locator roots before.workspace capacity budget → budget ≤ 65535 →
      3 ≤ roots.degree.val → roots.affine = false →
      roots.attempts.val + (64 - roots.direction.val) ≤ Usize.max →
      cacheWellFormed roots (buffersFor roots before.workspace) →
      TraceAgreement (activeFactor roots before.workspace) roots.splitter_seed roots.direction.val →
      before.meter.exhausted = false →
      before.meter.used.val + nodeEnvelope roots.degree.val ≤ before.meter.limit.val →
      ∃ (tries : Nat) (divider after : RootDrainState K) (frame : FactorFrame),
        0 < tries ∧ tries ≤ 64 - roots.direction.val ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          (2 * tries + 2) before after id ∧
        after.execution.state = .Running (ClosedLeafAdvance.stageFor after.execution.roots) ∧
        RootTraversalInvariant locator after.execution.roots after.workspace capacity budget ∧
        after.workspace.stack.val[divider.execution.roots.pending.val]? = some frame ∧
        frame.next_direction = after.execution.roots.direction ∧ frame.split_checked = 1#u32 ∧
        TraceAgreement (activeFactor after.execution.roots after.workspace)
          after.execution.roots.splitter_seed after.execution.roots.direction.val ∧
        TraceAgreement (pendingFactor after.workspace frame)
          after.execution.roots.splitter_seed frame.next_direction.val ∧
        after.meter.exhausted = false ∧ after.meter.limit = before.meter.limit ∧
        after.meter.used.val ≤ before.meter.used.val + nodeEnvelope roots.degree.val

theorem native_nonaffine_reducer_node : ActualNativeNonaffineReducerNode := by
  intro canonicalize K kernels scale backend raw square reduce mul inverse locator input before capacity budget
    roots state noProbe invariant budgetFit minimum affine attempts cache history live reserved
  let degree := roots.degree.val
  change before.meter.used.val + nodeEnvelope degree ≤ before.meter.limit.val at reserved
  have checks : (if roots.checked then 0 else splitCheckUnits degree) ≤ splitCheckUnits degree := by
    cases roots.checked <;> simp
  have pair := Nat.mul_le_mul_right (traceUnits degree + gcdUnits degree) (Nat.sub_le 64 roots.direction.val)
  have localReserve : tableUnits degree + traceSearchUnits degree roots.direction.val roots.checked +
      divideUnits degree + assemblyUnits degree ≤ nodeEnvelope degree := by
    rw [← node_envelope_expanded, traceSearchUnits]
    omega
  have room : before.meter.used.val + tableUnits degree + traceSearchUnits degree roots.direction.val roots.checked +
      divideUnits degree + assemblyUnits degree ≤ before.meter.limit.val := by omega
  obtain ⟨prepared, prep, ready, sameRoots, _, _, prepUsed, prepLimit⟩ :=
    native_nonaffine_reducer_ready canonicalize kernels scale backend locator input before capacity budget
      state noProbe invariant budgetFit minimum affine attempts cache history live (by
        change before.meter.used.val + tableUnits degree +
          traceSearchUnits degree roots.direction.val roots.checked ≤ before.meter.limit.val
        omega)
  change prepared.meter.used.val = before.meter.used.val + tableUnits degree at prepUsed
  have nextRoom : prepared.meter.used.val + traceSearchUnits prepared.execution.roots.degree.val
      prepared.execution.roots.direction.val prepared.execution.roots.checked +
      divideUnits prepared.execution.roots.degree.val + assemblyUnits prepared.execution.roots.degree.val ≤
        prepared.meter.limit.val := by
    rwa [sameRoots, prepUsed, prepLimit]
  obtain ⟨tries, divider, after, frame, positive, bounded, node, _, _, _, running, safe,
    saved, savedDirection, savedChecked, active, pending, finalLive, finalLimit, used, spent⟩ :=
      native_trace_node canonicalize kernels raw square reduce mul inverse scale locator input capacity budget
        prepared budgetFit ready nextRoom
  rw [sameRoots] at bounded used spent
  have joined := append_successful_chunks prep node
  refine ⟨tries, divider, after, frame, positive, bounded, ?_, running, safe, saved, savedDirection,
    savedChecked, active, pending, finalLive, finalLimit.trans prepLimit, ?_⟩
  · simpa only [Function.id_comp, show 1 + (2 * tries + 1) = 2 * tries + 2 by omega] using joined
  · rw [prepUsed] at used spent
    change after.meter.used.val -
      (before.meter.used.val + tableUnits degree) + tableUnits degree ≤ nodeEnvelope degree at spent
    change after.meter.used.val = before.meter.used.val + tableUnits degree +
      tries * (traceUnits degree + gcdUnits degree) +
      (if roots.checked then 0 else splitCheckUnits degree) + divideUnits degree + assemblyUnits degree at used
    change after.meter.used.val ≤ before.meter.used.val + nodeEnvelope degree
    omega

#print axioms native_nonaffine_reducer_node

#print axioms native_nonaffine_reducer_ready

end BulksketchBridge.RootRun
