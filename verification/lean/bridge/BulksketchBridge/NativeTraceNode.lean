import BulksketchBridge.NativeTraceSearch

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 DenseCoefficient SliceKernels RootTrace RootWorkBudget WorkSchedule
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open ExecutionDriver ExecutionDriverRuntime ExecutionFinish
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.stages bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private theorem checked_normal (units : Nat) (fits : units ≤ U64.max) :
    ∃ word, checkedCost units = .Ok word ∧ word.val = units := by
  rw [checkedCost, dite_eq_left fits]
  exact ⟨_, rfl, UScalar.ofNatCore_val_eq _⟩

private theorem divide_and_assembly_prices (degree : Usize) (fits : degree.val ≤ 65535) :
    RootDivide.divideCost degree = checkedCost (divideUnits degree.val) ∧
    RootDivide.assemblyCost degree = checkedCost (assemblyUnits degree.val) := by
  have w : degree.val + 1 ≤ 65536 := by omega
  have sq : (degree.val + 1) * (degree.val + 1) ≤ 65536 * 65536 := Nat.mul_le_mul w w
  obtain ⟨width, widthOk, widthVal⟩ := checked_normal (degree.val + 1) (by rw [U64.max_eq]; omega)
  obtain ⟨square, squareOk, squareVal⟩ := checked_normal ((degree.val + 1) * (degree.val + 1))
    (by rw [U64.max_eq]; omega)
  obtain ⟨work, workOk, workVal⟩ := checked_normal (4 * ((degree.val + 1) * (degree.val + 1)))
    (by rw [U64.max_eq]; omega)
  constructor
  · simp only [RootDivide.divideCost, widthOk, widthVal, squareOk, squareVal, workOk, workVal, divideUnits, pow_two]
  · simp only [RootDivide.assemblyCost, widthOk, widthVal, assemblyUnits]

private theorem paid_checked_cost (meter : WorkMeter) (units : Nat)
    (live : meter.exhausted = false) (room : meter.used.val + units ≤ meter.limit.val) :
    ∃ paid, StageCharge.chargeResult meter (checkedCost units) = (.Ok (), paid) ∧
      paid.used.val = meter.used.val + units ∧ paid.limit = meter.limit ∧ paid.exhausted = false := by
  obtain ⟨word, ok, value⟩ := checked_normal units (by have := meter.limit.le_max; rw [U64.max_eq] at *; omega)
  obtain ⟨paid, charged, used, limit, active⟩ :=
    WorkMeter.native_work_meter_paid meter word live (by rwa [value])
  rw [StageCharge.meter_charge_refines] at charged
  exact ⟨paid, by rw [ok]; exact Result.ok_injective charged, by rwa [value] at used, limit, active⟩

/-- One admitted non-affine factor finds its first separator and commits
both children with the exact native direction, stack and work updates. -/
def ActualNativeTraceNode : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    ∀ (locator : Polynomial Field) (input : RowInput) (capacity budget : Nat) (before : RootDrainState K),
      budget ≤ 65535 → TraceSearchReady kernels locator before capacity budget →
      let roots := before.execution.roots
      let degree := roots.degree.val
      before.meter.used.val + traceSearchUnits degree roots.direction.val roots.checked +
        divideUnits degree + assemblyUnits degree ≤ before.meter.limit.val →
      ∃ (tries : Nat) (middle after : RootDrainState K) (frame : FactorFrame),
        0 < tries ∧ tries ≤ 64 - roots.direction.val ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          (2 * tries + 1) before after id ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          (2 * tries) before middle id ∧
        TraceDivisionReady locator middle capacity budget ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          1 middle after id ∧
        after.execution.state = .Running (ClosedLeafAdvance.stageFor after.execution.roots) ∧
        RootTraversalInvariant locator after.execution.roots after.workspace capacity budget ∧
        after.workspace.stack.val[middle.execution.roots.pending.val]? = some frame ∧
        frame.next_direction = after.execution.roots.direction ∧ frame.split_checked = 1#u32 ∧
        TraceAgreement (activeFactor after.execution.roots after.workspace)
          after.execution.roots.splitter_seed after.execution.roots.direction.val ∧
        TraceAgreement (pendingFactor after.workspace frame)
          after.execution.roots.splitter_seed frame.next_direction.val ∧
        after.meter.exhausted = false ∧ after.meter.limit = before.meter.limit ∧
        after.meter.used.val = before.meter.used.val +
          tries * (traceUnits degree + gcdUnits degree) +
          (if roots.checked then 0 else splitCheckUnits degree) + divideUnits degree + assemblyUnits degree ∧
        after.meter.used.val - before.meter.used.val + tableUnits degree ≤ nodeEnvelope degree

/-- The complete source split node records enough exact metadata to
keep older siblings live and transfer the active factor's credits. -/
structure NativeTraceNodeFrame {K : Type} (before divider after : RootDrainState K)
    (frame : FactorFrame) (tries : Nat) : Prop where
  search : NativeTraceSearchFrame before divider
  split : RootDivide.NativeTraceSplitFrame divider.execution.roots after.execution.roots divider.workspace after.workspace frame
  degree : divider.execution.roots.degree = before.execution.roots.degree
  attempts : divider.execution.roots.attempts.val = before.execution.roots.attempts.val + tries
  budget : after.execution.budget = before.execution.budget
  noProbe : after.execution.degree_probe = none
  nonAffine : after.execution.roots.affine = false
  seed : after.execution.roots.splitter_seed = divider.execution.roots.splitter_seed
  basis : after.workspace.basis = divider.workspace.basis
  earlierWords : ∀ i < frame.coefficient_start.val, after.workspace.factors[i]! = divider.workspace.factors[i]!
  earlierStack : ∀ slot < divider.execution.roots.pending.val,
    after.workspace.stack.val[slot]? = divider.workspace.stack.val[slot]?

/-- One admitted non-affine factor finds its first separator and commits
both children with the exact native direction, stack and work updates. -/
def ActualNativeTraceNodeFrame : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    ∀ (locator : Polynomial Field) (input : RowInput) (capacity budget : Nat) (before : RootDrainState K),
      budget ≤ 65535 → TraceSearchReady kernels locator before capacity budget →
      let roots := before.execution.roots
      let degree := roots.degree.val
      before.meter.used.val + traceSearchUnits degree roots.direction.val roots.checked +
        divideUnits degree + assemblyUnits degree ≤ before.meter.limit.val →
      ∃ (tries : Nat) (middle after : RootDrainState K) (frame : FactorFrame),
        0 < tries ∧ tries ≤ 64 - roots.direction.val ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          (2 * tries + 1) before after id ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          (2 * tries) before middle id ∧
        TraceDivisionReady locator middle capacity budget ∧
        SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
          1 middle after id ∧
        after.execution.state = .Running (ClosedLeafAdvance.stageFor after.execution.roots) ∧
        RootTraversalInvariant locator after.execution.roots after.workspace capacity budget ∧
        after.workspace.stack.val[middle.execution.roots.pending.val]? = some frame ∧
        frame.next_direction = after.execution.roots.direction ∧ frame.split_checked = 1#u32 ∧
        TraceAgreement (activeFactor after.execution.roots after.workspace)
          after.execution.roots.splitter_seed after.execution.roots.direction.val ∧
        TraceAgreement (pendingFactor after.workspace frame)
          after.execution.roots.splitter_seed frame.next_direction.val ∧
        after.meter.exhausted = false ∧ after.meter.limit = before.meter.limit ∧
        after.meter.used.val = before.meter.used.val +
          tries * (traceUnits degree + gcdUnits degree) +
          (if roots.checked then 0 else splitCheckUnits degree) + divideUnits degree + assemblyUnits degree ∧
        after.meter.used.val - before.meter.used.val + tableUnits degree ≤ nodeEnvelope degree ∧
        NativeTraceNodeFrame before middle after frame tries

theorem native_trace_node_frame : ActualNativeTraceNodeFrame := by
  intro canonicalize K kernels raw square reduce mul inverse scale locator input capacity budget before
    budgetBound ready roots degree reserved
  obtain ⟨tries, middle, positive, bounded, searched, divider, degreeEq, _, attempts, live, limit, used, searchFrame⟩ :=
    native_trace_search_frame canonicalize kernels raw square reduce mul inverse scale locator input capacity budget
      before budgetBound ready
  have scanBound : tries * (traceUnits degree + gcdUnits degree) ≤
      (64 - roots.direction.val) * (traceUnits degree + gcdUnits degree) :=
    Nat.mul_le_mul_right _ bounded
  change before.meter.used.val + traceSearchUnits degree roots.direction.val roots.checked +
    divideUnits degree + assemblyUnits degree ≤ before.meter.limit.val at reserved
  unfold traceSearchUnits at reserved
  have room : middle.meter.used.val + divideUnits degree + assemblyUnits degree ≤ middle.meter.limit.val := by
    rw [used, limit]
    change before.meter.used.val + tries * (traceUnits degree + gcdUnits degree) +
      (if roots.checked then 0 else splitCheckUnits degree) + divideUnits degree + assemblyUnits degree ≤ _
    omega
  have fits := (traversal_degree_budget locator middle.execution.roots middle.workspace capacity budget
    divider.invariant).trans budgetBound
  obtain ⟨dividePrice, assemblyPrice⟩ := divide_and_assembly_prices middle.execution.roots.degree fits
  rw [degreeEq] at dividePrice assemblyPrice
  obtain ⟨paid, divideCharged, divideUsed, paidLimit, paidLive⟩ :=
    paid_checked_cost middle.meter (divideUnits degree) live (by omega)
  obtain ⟨finalMeter, assemblyCharged, finalUsed, finalLimit, finalLive⟩ :=
    paid_checked_cost paid (assemblyUnits degree) paidLive (by rw [divideUsed, paidLimit]; exact room)
  obtain ⟨afterRoots, written, frame, ran, invariant, _, nonAffine, _, seed, _, basis, read, direction,
    checked, earlierWords, earlierStack, history, pendingHistory, splitFrame⟩ :=
    RootDivide.native_trace_split_frame kernels locator middle.execution.roots middle.workspace middle.meter
      paid finalMeter capacity budget divider.invariant divider.nonAffine mul raw reduce inverse
      (by rw [degreeEq, dividePrice]; exact divideCharged) (by rw [degreeEq, assemblyPrice]; exact assemblyCharged)
      divider.frame divider.history divider.classified
  let next := ClosedLeafAdvance.stageFor afterRoots
  let after := advanceRootState middle next afterRoots written finalMeter
  have step := native_root_driver_return canonicalize kernels middle.execution .FactorDivision input middle.workspace
    middle.meter finalMeter (.Ok (.Ok next)) afterRoots written id divider.state divider.noProbe rfl ran
  have chunk : SuccessfulChunk (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
      1 middle after id :=
    SuccessfulChunk.step middle after after .FactorDivision (progress .FactorDivision { middle.execution with roots := afterRoots })
      id id 0 divider.state step (.empty after)
  have joined := append_successful_chunks searched chunk
  have debit : finalMeter.used.val = before.meter.used.val +
      tries * (traceUnits degree + gcdUnits degree) +
      (if roots.checked then 0 else splitCheckUnits degree) + divideUnits degree + assemblyUnits degree :=
    finalUsed.trans (by rw [divideUsed, used])
  refine ⟨tries, middle, after, frame, positive, bounded, joined, searched, divider, chunk, rfl,
    invariant, read, direction, checked, history, pendingHistory, finalLive,
    finalLimit.trans (paidLimit.trans limit), debit, ?_,
    ⟨searchFrame, splitFrame, degreeEq, attempts, searchFrame.budget, divider.noProbe, nonAffine, seed, basis, earlierWords, earlierStack⟩⟩
  have attemptsBound : tries ≤ 64 := bounded.trans (Nat.sub_le ..)
  have pairBound := Nat.mul_le_mul_right (traceUnits degree + gcdUnits degree) attemptsBound
  have checkBound : (if roots.checked then 0 else splitCheckUnits degree) ≤ splitCheckUnits degree := by
    cases roots.checked <;> simp
  change finalMeter.used.val - before.meter.used.val + tableUnits degree ≤ nodeEnvelope degree
  rw [debit, ← node_envelope_expanded]
  omega

theorem native_trace_node : ActualNativeTraceNode := by
  intro canonicalize K kernels raw square reduce mul inverse scale locator input capacity budget before
    budgetBound ready roots degree reserved
  obtain ⟨tries, middle, after, frame, positive, bounded, joined, searched, divider, chunk, running,
    invariant, read, direction, checked, history, pendingHistory, live, limit, debit, spent, _⟩ :=
    native_trace_node_frame canonicalize kernels raw square reduce mul inverse scale locator input capacity budget
      before budgetBound ready reserved
  exact ⟨tries, middle, after, frame, positive, bounded, joined, searched, divider, chunk, running,
    invariant, read, direction, checked, history, pendingHistory, live, limit, debit, spent⟩

#print axioms native_trace_node_frame
#print axioms native_trace_node

end BulksketchBridge.RootRun
