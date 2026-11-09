import BulksketchBridge.RootTraceInvariant
import BulksketchBridge.RootGcdInvariant
import BulksketchBridge.RootTraversalFactor

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient RootTrace
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec RebuiltLfsr BmEntry
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private theorem gcd_retains_trace_configuration (roots : Roots) (buffers : FactorWork)
    (size : Usize) (nonAffine : roots.affine = false) :
    let after := (outcome roots buffers size).2
    after.degree = roots.degree ∧ after.trace_len = roots.trace_len ∧
    after.splitter_seed = roots.splitter_seed ∧ after.affine = false := by
  dsimp only
  by_cases proper : 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val
  · simp only [outcome, proper, ite_true, nonAffine, and_self]
  · simp only [outcome, proper, ite_false, nonAffine, Bool.false_eq_true, and_self]

/-- Paid original non-affine Trace and GCD compose through the exact
normalized trace window. A retry preserves its reducer and direction
cache, while a proper result supplies the original division frame. -/
def ActualNativeTraceGcdPair : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid traced finalMeter : WorkMeter) (capacity budget : Nat),
    RootTraversalInvariant locator roots workspace capacity budget → 3 ≤ roots.degree.val →
    roots.affine = false → roots.attempts.val + 1 ≤ Usize.max →
    charge meter (.Trace roots.degree) = .ok (.Ok (), paid) →
    (if roots.checked then traced = paid
      else charge paid (.SplitCheck roots.degree) = .ok (.Ok (), traced)) →
    charge traced (.Gcd roots.degree) = .ok (.Ok (), finalMeter) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    let before := buffersFor roots workspace
    cacheWellFormed roots before → CorrectTable before.modulus before.table roots.degree.val →
    BackendSquareLaw kernels before.modulus before.table roots.degree.val →
    TraceAgreement (activeFactor roots workspace) roots.splitter_seed roots.direction.val →
    ∃ (tracedRoots after : Roots) (tracedWorkspace written : RowWorkspace) (next : Stage),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Trace workspace meter =
        .ok (.Ok (.Ok .Gcd), tracedRoots, tracedWorkspace, id, traced) ∧
      Roots.run nativeCalls nativeDivRem dictionary kernels tracedRoots .Gcd tracedWorkspace traced =
        .ok (.Ok (.Ok next), after, written, id, finalMeter) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      activeFactor after written = activeFactor roots workspace ∧
      after.splitter_seed = roots.splitter_seed ∧ after.affine = false ∧
      traversalRank next after written < traversalRank .Trace roots workspace ∧
      let buffers := buffersFor after written
      CorrectTable buffers.modulus buffers.table after.degree.val ∧ cacheWellFormed after buffers ∧
      (next = .FactorDivision ∧
        RootDivide.ProperGcdFrame after buffers (slicePolynomial (prefixSlice buffers.trace after.trace_len.val)) ∨
       next = .Trace ∧ TraceAgreement (activeFactor after written) after.splitter_seed after.direction.val)

/-- The exact Trace/GCD pair preserves both the original retry charge
schedule and the trace classification needed by proper division. -/
def ActualNativeTraceGcdDivisionReady : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid traced finalMeter : WorkMeter) (capacity budget : Nat),
    RootTraversalInvariant locator roots workspace capacity budget → 3 ≤ roots.degree.val →
    roots.affine = false → roots.attempts.val + 1 ≤ Usize.max →
    charge meter (.Trace roots.degree) = .ok (.Ok (), paid) →
    (if roots.checked then traced = paid
      else charge paid (.SplitCheck roots.degree) = .ok (.Ok (), traced)) →
    charge traced (.Gcd roots.degree) = .ok (.Ok (), finalMeter) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    let before := buffersFor roots workspace
    cacheWellFormed roots before → CorrectTable before.modulus before.table roots.degree.val →
    BackendSquareLaw kernels before.modulus before.table roots.degree.val →
    TraceAgreement (activeFactor roots workspace) roots.splitter_seed roots.direction.val →
    ∃ (tracedRoots after : Roots) (tracedWorkspace written : RowWorkspace) (next : Stage),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Trace workspace meter =
        .ok (.Ok (.Ok .Gcd), tracedRoots, tracedWorkspace, id, traced) ∧
      Roots.run nativeCalls nativeDivRem dictionary kernels tracedRoots .Gcd tracedWorkspace traced =
        .ok (.Ok (.Ok next), after, written, id, finalMeter) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      activeFactor after written = activeFactor roots workspace ∧
      after.splitter_seed = roots.splitter_seed ∧ after.affine = false ∧
      traversalRank next after written < traversalRank .Trace roots workspace ∧
      after.degree = roots.degree ∧ after.attempts.val = roots.attempts.val + 1 ∧ after.checked = true ∧
      written.stack = workspace.stack ∧ written.factors = workspace.factors ∧
      let buffers := buffersFor after written
      let trace := slicePolynomial (prefixSlice buffers.trace after.trace_len.val)
      CorrectTable buffers.modulus buffers.table after.degree.val ∧ cacheWellFormed after buffers ∧
      BackendSquareLaw kernels buffers.modulus buffers.table after.degree.val ∧
      (next = .FactorDivision ∧ after.direction = roots.direction ∧
        RootDivide.ProperGcdFrame after buffers trace ∧
        TraceAgreement (activeFactor after written) after.splitter_seed after.direction.val ∧
        (∀ point, (activeFactor after written).IsRoot point →
          (trace.IsRoot point ↔ traceBit after.splitter_seed after.direction.val point = 0)) ∨
       next = .Trace ∧ after.direction.val = roots.direction.val + 1 ∧
        TraceAgreement (activeFactor after written) after.splitter_seed after.direction.val)

/-- Fields the original Trace/GCD pair leaves unchanged while it
searches for a proper divisor. -/
structure NativeTraceFixedFrame (roots after : Roots) (workspace written : RowWorkspace) : Prop where
  pending : after.pending = roots.pending
  count : after.count = roots.count
  stride : after.stride = roots.stride
  closedForm : after.closed_form = roots.closed_form
  widths : workspaceLengths written = workspaceLengths workspace

/-- The exact Trace/GCD pair preserves both the original retry charge
schedule and the trace classification needed by proper division. -/
def ActualNativeTraceGcdFixedFrame : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid traced finalMeter : WorkMeter) (capacity budget : Nat),
    RootTraversalInvariant locator roots workspace capacity budget → 3 ≤ roots.degree.val →
    roots.affine = false → roots.attempts.val + 1 ≤ Usize.max →
    charge meter (.Trace roots.degree) = .ok (.Ok (), paid) →
    (if roots.checked then traced = paid
      else charge paid (.SplitCheck roots.degree) = .ok (.Ok (), traced)) →
    charge traced (.Gcd roots.degree) = .ok (.Ok (), finalMeter) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    let before := buffersFor roots workspace
    cacheWellFormed roots before → CorrectTable before.modulus before.table roots.degree.val →
    BackendSquareLaw kernels before.modulus before.table roots.degree.val →
    TraceAgreement (activeFactor roots workspace) roots.splitter_seed roots.direction.val →
    ∃ (tracedRoots after : Roots) (tracedWorkspace written : RowWorkspace) (next : Stage),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Trace workspace meter =
        .ok (.Ok (.Ok .Gcd), tracedRoots, tracedWorkspace, id, traced) ∧
      Roots.run nativeCalls nativeDivRem dictionary kernels tracedRoots .Gcd tracedWorkspace traced =
        .ok (.Ok (.Ok next), after, written, id, finalMeter) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      activeFactor after written = activeFactor roots workspace ∧
      after.splitter_seed = roots.splitter_seed ∧ after.affine = false ∧
      traversalRank next after written < traversalRank .Trace roots workspace ∧
      after.degree = roots.degree ∧ after.attempts.val = roots.attempts.val + 1 ∧ after.checked = true ∧
      written.stack = workspace.stack ∧ written.factors = workspace.factors ∧
      NativeTraceFixedFrame roots after workspace written ∧
      let buffers := buffersFor after written
      let trace := slicePolynomial (prefixSlice buffers.trace after.trace_len.val)
      CorrectTable buffers.modulus buffers.table after.degree.val ∧ cacheWellFormed after buffers ∧
      BackendSquareLaw kernels buffers.modulus buffers.table after.degree.val ∧
      (next = .FactorDivision ∧ after.direction = roots.direction ∧
        RootDivide.ProperGcdFrame after buffers trace ∧
        TraceAgreement (activeFactor after written) after.splitter_seed after.direction.val ∧
        (∀ point, (activeFactor after written).IsRoot point →
          (trace.IsRoot point ↔ traceBit after.splitter_seed after.direction.val point = 0)) ∨
       next = .Trace ∧ after.direction.val = roots.direction.val + 1 ∧
        TraceAgreement (activeFactor after written) after.splitter_seed after.direction.val)

theorem native_trace_gcd_fixed_frame : ActualNativeTraceGcdFixedFrame := by
  intro K kernels locator roots workspace meter paid traced finalMeter capacity budget invariant minimum
    nonAffine counter chargeTrace splitCharge chargeGcd rawLaw squareLaw reduceLaw mul inverse scale
    before cache table backend agreement
  obtain ⟨writes, traceRan, traceInvariant, traceFactor, traceReborrow, traceTable, traceCache, traceAttempts, traceRoom, normal,
    traceRank, traceWidths, classifies⟩ :=
    native_trace_invariant_widths kernels locator roots workspace meter paid traced capacity budget invariant
      minimum counter chargeTrace splitCharge rawLaw squareLaw reduceLaw cache table backend agreement
  let tracedFrame := writes.frame roots before true (.Ok (.Ok .Gcd)) traced
  let tracedRoots := tracedFrame.2.1
  let tracedWorkspace := rebuild workspace roots tracedFrame.2.2.1
  let tracedBuffers := buffersFor tracedRoots tracedWorkspace
  let trace := slicePolynomial (prefixSlice tracedBuffers.trace tracedRoots.trace_len.val)
  have traceAgreement : TraceAgreement (activeFactor tracedRoots tracedWorkspace)
      tracedRoots.splitter_seed tracedRoots.direction.val := by
    change TraceAgreement (activeFactor tracedRoots tracedWorkspace) roots.splitter_seed roots.direction.val
    rw [traceFactor]
    exact agreement
  have tracedMinimum : 3 ≤ tracedRoots.degree.val := minimum
  have positive : 0 < tracedRoots.degree.val := by omega
  obtain ⟨monic, exactDegree, split, simple, _⟩ := traceInvariant.active positive
  have enough : 2 ≤ (activeFactor tracedRoots tracedWorkspace).natDegree := by
    change (activeFactor tracedRoots tracedWorkspace).natDegree = tracedRoots.degree.val at exactDegree
    rw [exactDegree]
    omega
  have direction := trace_agreement_before_end (activeFactor tracedRoots tracedWorkspace)
    tracedRoots.splitter_seed tracedRoots.direction.val monic.ne_zero split simple enough traceAgreement
  obtain ⟨size, result, work, raw, gcdRan, gcdInvariant, gcdReborrow, gcdRawWidth, gcdRank, _, _, proper, retry⟩ :=
    native_gcd_invariant kernels tracedRoots tracedWorkspace traced finalMeter locator capacity budget traceInvariant
      (by omega) traceRoom chargeGcd mul rawLaw reduceLaw inverse scale
      (traversal_modulus_normal locator tracedRoots tracedWorkspace capacity budget traceInvariant (by omega))
      normal (by simp [tracedRoots, tracedFrame, TraceWrites.frame, nonAffine]) (fun _ => direction)
  let output := outcome tracedRoots tracedBuffers size
  let after := output.2
  let written := rebuild tracedWorkspace tracedRoots { tracedBuffers with gcd := result, work, raw }
  obtain ⟨degree, traceLen, seed, affine⟩ :=
    gcd_retains_trace_configuration tracedRoots tracedBuffers size nonAffine
  have sameFactor : activeFactor after written = activeFactor tracedRoots tracedWorkspace := by
    change slicePolynomial (buffersFor after written).modulus = _
    rw [gcdReborrow]
    rfl
  have correct : CorrectTable (buffersFor after written).modulus (buffersFor after written).table after.degree.val := by
    rw [gcdReborrow, degree]
    exact traceTable
  have cached : cacheWellFormed after (buffersFor after written) := by
    rw [gcdReborrow]
    unfold cacheWellFormed
    rw [seed]
    exact traceCache
  have tracedAffine : tracedRoots.affine = false := nonAffine
  have noAffine : ¬ tracedRoots.affine = true := by rw [tracedAffine]; decide
  have keep : after.attempts = tracedRoots.attempts ∧ after.checked = tracedRoots.checked := by
    change (outcome tracedRoots tracedBuffers size).2.attempts = tracedRoots.attempts ∧
      (outcome tracedRoots tracedBuffers size).2.checked = tracedRoots.checked
    by_cases condition : 0 < size.val - 1 ∧ size.val - 1 < tracedRoots.degree.val
    · rw [outcome, ite_eq_left condition]
      exact ⟨rfl, rfl⟩
    · rw [outcome, ite_eq_right condition, ite_eq_right noAffine]
      exact ⟨rfl, rfl⟩
  have checked : after.checked = true := keep.2.trans rfl
  change tracedBuffers = tracedFrame.2.2.1 at traceReborrow
  have backendAfter : BackendSquareLaw kernels (buffersFor after written).modulus
      (buffersFor after written).table after.degree.val := by
    rw [gcdReborrow, degree]
    have tableFrame : tracedBuffers.table = before.table := by rw [traceReborrow]; rfl
    have modulusFrame : tracedBuffers.modulus = before.modulus := by rw [traceReborrow]; rfl
    rw [tableFrame, modulusFrame]
    exact backend
  have sameShape : after.pending = roots.pending ∧ after.count = roots.count ∧
      after.stride = roots.stride ∧ after.closed_form = roots.closed_form := by
    change (outcome tracedRoots tracedBuffers size).2.pending = roots.pending ∧
      (outcome tracedRoots tracedBuffers size).2.count = roots.count ∧
      (outcome tracedRoots tracedBuffers size).2.stride = roots.stride ∧
      (outcome tracedRoots tracedBuffers size).2.closed_form = roots.closed_form
    by_cases condition : 0 < size.val - 1 ∧ size.val - 1 < tracedRoots.degree.val
    · rw [outcome, ite_eq_left condition]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [outcome, ite_eq_right condition, ite_eq_right noAffine]
      exact ⟨rfl, rfl, rfl, rfl⟩
  have sameWidths : workspaceLengths written = workspaceLengths workspace := by
    calc
      _ = workspaceLengths tracedWorkspace := by
        simp only [written, workspaceLengths, rebuild, RootSetup.restoreWork, splitBack_length, restore_length]
        exact congrArg (fun n => (⟨tracedWorkspace.syndromes.length, tracedWorkspace.bm.length,
          tracedWorkspace.polynomials.length, tracedWorkspace.factors.length, tracedWorkspace.square_table.length,
          tracedWorkspace.verification.length, tracedWorkspace.roots.length, n, tracedWorkspace.stack.length⟩ :
          WorkspaceAdmission.Lengths)) gcdRawWidth
      _ = _ := traceWidths
  have fixed : NativeTraceFixedFrame roots after workspace written :=
    ⟨sameShape.1, sameShape.2.1, sameShape.2.2.1, sameShape.2.2.2, sameWidths⟩
  have tracedDirection : tracedRoots.direction = roots.direction := rfl
  have sameTrace : slicePolynomial (prefixSlice (buffersFor after written).trace after.trace_len.val) = trace := by
    rw [gcdReborrow, traceLen]
  by_cases divides : Proper tracedRoots size
  · obtain ⟨chosen, frame⟩ := proper divides
    have sameDirection : after.direction = roots.direction := by
      have condition : 0 < size.val - 1 ∧ size.val - 1 < tracedRoots.degree.val := divides
      change (outcome tracedRoots tracedBuffers size).2.direction = roots.direction
      rw [outcome, ite_eq_left condition]
      exact tracedDirection
    refine ⟨tracedRoots, after, tracedWorkspace, written, .FactorDivision, traceRan, ?_, gcdInvariant,
      sameFactor.trans traceFactor, seed, affine, (gcdRank _ chosen).trans traceRank,
      degree, (congrArg UScalar.val keep.1).trans traceAttempts, checked, rfl, rfl, fixed,
      correct, cached, backendAfter, Or.inl ⟨rfl, sameDirection, ?_, ?_, ?_⟩⟩
    · rw [← chosen]
      exact gcdRan
    · rwa [sameTrace]
    · rw [sameFactor, seed, sameDirection, traceFactor]
      exact agreement
    · intro point isRoot
      rw [sameTrace, seed, sameDirection]
      exact classifies point (sameFactor ▸ isRoot)
  · obtain ⟨chosen, _, valid⟩ := retry nonAffine divides split simple traceAgreement classifies
    have condition : ¬ (0 < size.val - 1 ∧ size.val - 1 < tracedRoots.degree.val) := divides
    have stepped : after.direction = nextDirection tracedRoots := by
      change (outcome tracedRoots tracedBuffers size).2.direction = nextDirection tracedRoots
      rw [outcome, ite_eq_right condition, ite_eq_right noAffine]
    have nextVal : after.direction.val = roots.direction.val + 1 := by
      rw [stepped, ← U32.bv_toNat]
      change (BitVec.ofNat 32 (tracedRoots.direction.val + 1)).toNat = _
      rw [BitVec.toNat_ofNat, tracedDirection, Nat.mod_eq_of_lt]
      rw [tracedDirection] at direction
      omega
    refine ⟨tracedRoots, after, tracedWorkspace, written, .Trace, traceRan, ?_, gcdInvariant,
      sameFactor.trans traceFactor, seed, affine, (gcdRank _ chosen).trans traceRank,
      degree, (congrArg UScalar.val keep.1).trans traceAttempts, checked, rfl, rfl, fixed,
      correct, cached, backendAfter, Or.inr ⟨rfl, nextVal, ?_⟩⟩
    · rw [← chosen]
      exact gcdRan
    · rw [sameFactor, seed]
      exact valid

theorem native_trace_gcd_division_ready : ActualNativeTraceGcdDivisionReady := by
  intro K kernels locator roots workspace meter paid traced finalMeter capacity budget invariant minimum
    nonAffine counter chargeTrace splitCharge chargeGcd raw square reduce mul inverse scale
    before cache table backend agreement
  obtain ⟨tracedRoots, after, tracedWorkspace, written, next, traceRan, gcdRan, retained,
    factor, seed, affine, rank, degree, attempts, checked, stack, factors, _, correct, cached, squareLaw, outcome⟩ :=
    native_trace_gcd_fixed_frame kernels locator roots workspace meter paid traced finalMeter capacity budget
      invariant minimum nonAffine counter chargeTrace splitCharge chargeGcd raw square reduce
      mul inverse scale cache table backend agreement
  exact ⟨tracedRoots, after, tracedWorkspace, written, next, traceRan, gcdRan, retained,
    factor, seed, affine, rank, degree, attempts, checked, stack, factors, correct, cached, squareLaw, outcome⟩

#print axioms native_trace_gcd_fixed_frame

theorem native_trace_gcd_pair : ActualNativeTraceGcdPair := by
  intro K kernels locator roots workspace meter paid traced finalMeter capacity budget invariant minimum
    nonAffine counter chargeTrace splitCharge chargeGcd rawLaw squareLaw reduceLaw mul inverse scale
    before cache table backend agreement
  obtain ⟨tracedRoots, after, tracedWorkspace, written, next, traceRan, gcdRan, retained,
    factor, seed, affine, rank, _, _, _, _, _, correct, cached, _, outcome⟩ :=
    native_trace_gcd_division_ready kernels locator roots workspace meter paid traced finalMeter capacity budget
      invariant minimum nonAffine counter chargeTrace splitCharge chargeGcd rawLaw squareLaw reduceLaw
      mul inverse scale cache table backend agreement
  refine ⟨tracedRoots, after, tracedWorkspace, written, next, traceRan, gcdRan, retained,
    factor, seed, affine, rank, correct, cached, ?_⟩
  rcases outcome with ⟨proper, _, frame, _, _⟩ | ⟨retry, _, history⟩
  · exact Or.inl ⟨proper, frame⟩
  · exact Or.inr ⟨retry, history⟩

#print axioms native_trace_gcd_division_ready
#print axioms native_trace_gcd_pair

end BulksketchBridge.RootRun
