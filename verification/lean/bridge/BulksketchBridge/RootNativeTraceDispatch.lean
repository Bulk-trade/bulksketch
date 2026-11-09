import BulksketchBridge.RootNativeTraceCheck
import BulksketchBridge.RootWorkspaceBudget
import BulksketchBridge.NativeRootRun

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient RootTrace
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- The original paid non-affine trace dispatch enters GCD. The cached
directions and live factor supply direction admission, and the original
unchecked split test succeeds on a split simple factor. -/
def ActualNativeTraceDispatch : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid finalMeter : WorkMeter)
    (capacity budget : Nat),
    BudgetBuffers workspace capacity budget → 3 ≤ roots.degree.val → roots.degree.val ≤ budget →
    roots.attempts.val + 1 ≤ Usize.max →
    bulksketch.decode.roots.charge meter (.Trace roots.degree) = .ok (.Ok (), paid) →
    (if roots.checked then finalMeter = paid
      else bulksketch.decode.roots.charge paid (.SplitCheck roots.degree) = .ok (.Ok (), finalMeter)) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    let buffers := buffersFor roots workspace
    let factor := slicePolynomial buffers.modulus
    cacheWellFormed roots buffers → buffers.modulus[roots.degree.val]! = 1#u64 →
    CorrectTable buffers.modulus buffers.table roots.degree.val →
    BackendSquareLaw kernels buffers.modulus buffers.table roots.degree.val →
    factor.Splits → factor.roots.Nodup →
    TraceAgreement factor roots.splitter_seed roots.direction.val →
    ∃ writes : TraceWrites,
      let frame := writes.frame roots buffers true (.Ok (.Ok .Gcd)) finalMeter
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Trace workspace meter =
        .ok (frame.1, frame.2.1, rebuild workspace roots frame.2.2.1, id, finalMeter) ∧
      writes.correct roots buffers ∧
      ∀ point, factor.IsRoot point →
        ((slicePolynomial (prefixSlice writes.trace writes.activeLength.val)).IsRoot point ↔
          traceBit roots.splitter_seed roots.direction.val point = 0)

theorem native_trace_dispatch : ActualNativeTraceDispatch := by
  intro K kernels roots workspace meter paid finalMeter capacity budget sized degreeMin degreeBound
    counter charged splitCharge rawLaw squareLaw reduceLaw buffers factor cache monic tableCorrect backend
    split simple agreement
  obtain ⟨ready, modulusWidth, traceWidth, gcdWidth, _, rawWidth⟩ :=
    gcd_buffers_of_budget roots workspace capacity budget sized (by omega) degreeBound
  change buffers.modulus.length = roots.degree.val + 1 at modulusWidth
  change buffers.trace.length = roots.degree.val at traceWidth
  change buffers.gcd.length = roots.degree.val + 1 at gcdWidth
  change 2 * (roots.degree.val + 2) ≤ buffers.raw.length at rawWidth
  have tableWidth : buffers.table.length = roots.degree.val * (roots.degree.val / 2) := by
    change (prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val)).length = _
    rw [RebuiltLfsr.prefix_length, Nat.min_eq_left ready.2]
    rfl
  obtain ⟨factorMonic, factorDegree⟩ := modulus_monic buffers.modulus roots.degree.val modulusWidth monic
  have degree : factor.natDegree = roots.degree.val := natDegree_eq_of_degree_eq_some factorDegree
  have direction := trace_agreement_before_end factor roots.splitter_seed roots.direction.val
    factorMonic.ne_zero split simple (by omega) agreement
  have traceReady : TraceReady roots buffers :=
    ⟨counter, direction, cache, by omega, by omega, by omega, by omega⟩
  have minimum : 4 ≤ buffers.modulus.length := by omega
  obtain ⟨writes, sound, ran⟩ :
      ∃ writes : TraceWrites, writes.correct roots buffers ∧
        Roots.trace nativeSquare gf64 kernels roots buffers meter =
          .ok (writes.frame roots buffers true (.Ok (.Ok .Gcd)) finalMeter) := by
    cases checked : roots.checked with
    | true =>
      have exactMeter : finalMeter = paid := by simpa only [checked, ite_true] using splitCharge
      rw [exactMeter]
      have square := native_modular_square kernels rawLaw squareLaw reduceLaw buffers.modulus buffers.table
        roots.degree.val minimum modulusWidth monic tableWidth tableCorrect backend
      obtain ⟨attempts, basisLen, basis, size, trace, gcd, raw, native, data⟩ :=
        trace_checked_refines nativeSquare kernels roots buffers meter paid charged checked counter direction cache
          traceReady.trace traceReady.gcd traceReady.raw (by rwa [traceWidth])
      exact ⟨⟨attempts, basisLen, basis, size, trace, gcd, raw⟩, data, by simpa only [TraceWrites.frame, checked] using native⟩
    | false =>
      have second : bulksketch.decode.roots.charge paid (.SplitCheck roots.degree) = .ok (.Ok (), finalMeter) := by
        simpa only [checked, Bool.false_eq_true, ite_false] using splitCharge
      exact native_trace_check_accepts kernels roots buffers meter paid finalMeter checked traceReady charged second
        rawLaw squareLaw reduceLaw traceWidth minimum (by rwa [traceWidth]) (by rwa [traceWidth])
        (by rwa [traceWidth]) (by rwa [traceWidth]) (by rwa [traceWidth]) split simple
  refine ⟨writes, ?_, sound, trace_invariant_classifies buffers.modulus writes.trace writes.activeLength
    roots.splitter_seed roots.direction.val sound.2.2.2.2.2.2.2.2.2⟩
  rw [original_root_run_refines kernels roots .Trace workspace meter ready]
  unfold expected
  rw [ran]
  simp only [bind_ok]
  rfl

#print axioms native_trace_dispatch

end BulksketchBridge.RootRun
