import BulksketchBridge.RootTraceInvariant
import BulksketchBridge.RootGcdInvariant
import BulksketchBridge.RootTraversalFactor

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient RootTrace
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
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

theorem native_trace_gcd_pair : ActualNativeTraceGcdPair := by
  intro K kernels locator roots workspace meter paid traced finalMeter capacity budget invariant minimum
    nonAffine counter chargeTrace splitCharge chargeGcd rawLaw squareLaw reduceLaw mul inverse scale
    before cache table backend agreement
  obtain ⟨writes, traceRan, traceInvariant, traceFactor, _, traceTable, traceCache, _, traceRoom, normal,
    traceRank, classifies⟩ :=
    native_trace_invariant kernels locator roots workspace meter paid traced capacity budget invariant
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
  obtain ⟨size, result, work, raw, gcdRan, gcdInvariant, gcdReborrow, _, gcdRank, _, _, proper, retry⟩ :=
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
  by_cases divides : Proper tracedRoots size
  · obtain ⟨chosen, frame⟩ := proper divides
    refine ⟨tracedRoots, after, tracedWorkspace, written, .FactorDivision, traceRan, ?_, gcdInvariant,
      sameFactor.trans traceFactor, seed, affine, (gcdRank _ chosen).trans traceRank,
      correct, cached, Or.inl ⟨rfl, ?_⟩⟩
    · rw [← chosen]
      exact gcdRan
    · have sameTrace : slicePolynomial (prefixSlice (buffersFor after written).trace after.trace_len.val) = trace := by
        rw [gcdReborrow, traceLen]
      rwa [sameTrace]
  · obtain ⟨chosen, _, valid⟩ := retry nonAffine divides split simple traceAgreement classifies
    refine ⟨tracedRoots, after, tracedWorkspace, written, .Trace, traceRan, ?_, gcdInvariant,
      sameFactor.trans traceFactor, seed, affine, (gcdRank _ chosen).trans traceRank,
      correct, cached, Or.inr ⟨rfl, ?_⟩⟩
    · rw [← chosen]
      exact gcdRan
    · rw [sameFactor, seed]
      exact valid

#print axioms native_trace_gcd_pair

end BulksketchBridge.RootRun
