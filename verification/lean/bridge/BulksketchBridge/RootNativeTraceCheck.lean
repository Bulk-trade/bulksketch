import BulksketchBridge.RootTraceSplitAlgebra
import BulksketchBridge.RootTraceWrapper
import BulksketchBridge.NativeRootTrace

namespace BulksketchBridge.RootTrace

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient SliceKernels RebuiltLfsr
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- For a split simple modulus, the paid original trace check accepts
its exact padded polynomial and enters the GCD stage. -/
def ActualNativeTraceCheckAccept : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (buffers : FactorWork) (meter paid finalMeter : WorkMeter),
    roots.checked = false → TraceReady roots buffers →
    bulksketch.decode.roots.charge meter (.Trace roots.degree) = .ok (.Ok (), paid) →
    bulksketch.decode.roots.charge paid (.SplitCheck roots.degree) = .ok (.Ok (), finalMeter) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    buffers.trace.length = roots.degree.val →
    4 ≤ buffers.modulus.length → buffers.modulus.length = buffers.trace.length + 1 →
    buffers.modulus[buffers.trace.length]! = 1#u64 →
    buffers.table.length = buffers.trace.length * (buffers.trace.length / 2) →
    CorrectTable buffers.modulus buffers.table buffers.trace.length →
    BackendSquareLaw kernels buffers.modulus buffers.table buffers.trace.length →
    (slicePolynomial buffers.modulus).Splits → (slicePolynomial buffers.modulus).roots.Nodup →
    ∃ writes : TraceWrites, writes.correct roots buffers ∧
      Roots.trace nativeSquare gf64 kernels roots buffers meter =
        .ok (writes.frame roots buffers true (.Ok (.Ok .Gcd)) finalMeter)

theorem native_trace_check_accepts : ActualNativeTraceCheckAccept := by
  intro K kernels roots buffers meter paid finalMeter checked ready charged splitCharged
    rawLaw squareLaw reduceLaw traceWidth minimum shape monic tableLen tableCorrect backend split simple
  let degree := buffers.trace.length
  have square := native_modular_square kernels rawLaw squareLaw reduceLaw buffers.modulus buffers.table degree
    minimum shape monic tableLen tableCorrect backend
  have fullSquare := AffineSplitter.native_full_square kernels rawLaw squareLaw reduceLaw buffers.modulus
    buffers.table degree minimum shape monic tableLen tableCorrect backend
  obtain ⟨attempts, basisLen, basis, size, trace, gcd, raw, ran, attempt, live, cacheLen, cacheBound, cached,
    sizeRoom, traceLen, gcdLen, rawLen, invariant, before, checkDst, checkRaw, checkedSize, beforeWidth,
    dstWidth, checkRawWidth, padded, checkRan⟩ :=
    trace_split_checked_evidence nativeSquare kernels roots buffers meter paid finalMeter charged splitCharged
      ready.compare checked ready.counter ready.direction ready.cache ready.trace ready.gcd ready.raw square
  have inputRoom : (prefixSlice before size.val).length ≤ degree := by rw [prefix_length]; omega
  have dstRoom : degree ≤ checkDst.length := by rw [dstWidth]; exact ready.gcd
  have rawRoom : 2 * degree < checkRaw.length := by rw [checkRawWidth]; exact ready.raw
  obtain ⟨fullSize, fullGcd, fullRaw, fullRan, _, _, poly⟩ :=
    fullSquare (prefixSlice before size.val) checkDst checkRaw inputRoom dstRoom rawRoom
  have exactOutput := Result.ok_injective (fullRan.symm.trans checkRan)
  have gcdEq := congrArg (fun output => output.2.1) exactOutput
  change fullGcd = gcd at gcdEq
  rw [gcdEq] at poly
  have beforeRoom : size.val ≤ before.length := by omega
  have tracePoly := polynomial_of_zero_padding trace before size.val beforeRoom padded
  obtain ⟨factorMonic, factorDegree⟩ := modulus_monic buffers.modulus degree shape monic
  have exactDegree : (slicePolynomial buffers.modulus).natDegree = degree := natDegree_eq_of_degree_eq_some factorDegree
  have traceDegree : (slicePolynomial trace).natDegree < (slicePolynomial buffers.modulus).natDegree := by
    rw [exactDegree]
    have positive : 0 < degree := by have := ready.trace; omega
    apply lt_of_le_of_lt ?_ (show degree - 1 < degree by omega)
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i large
    rw [slicePolynomial_coeff, ite_eq_right (by omega)]
  have binary (point : Field) (root : (slicePolynomial buffers.modulus).IsRoot point) :
      (slicePolynomial trace).eval point = 0 ∨ (slicePolynomial trace).eval point = 1 := by
    have same : prefixSlice trace size.val = prefixSlice before size.val := by
      apply Slice.ext
      simp only [prefixSlice, Slice.from_val, padded]
      rw [List.take_append_of_le_length (by rw [List.length_take, Nat.min_eq_left beforeRoom]),
        List.take_take, Nat.min_self]
    have eq : slicePolynomial trace = slicePolynomial (prefixSlice trace size.val) :=
      tracePoly.trans (congrArg slicePolynomial same.symm)
    rw [eq]
    exact trace_value_binary buffers.modulus trace size (basisWord roots.splitter_seed roots.direction.val)
      invariant point root
  have fixed := trace_mod_square_idempotent (slicePolynomial buffers.modulus) (slicePolynomial trace)
    factorMonic split simple traceDegree binary
  have checkPoly : slicePolynomial (prefixSlice gcd roots.degree.val) = slicePolynomial trace := by
    rw [← traceWidth]
    change slicePolynomial (prefixSlice gcd degree) = _
    rw [poly, ← tracePoly]
    exact fixed
  have checkWidth : (prefixSlice gcd roots.degree.val).length = trace.length := by
    rw [prefix_length, gcdLen, Nat.min_eq_left ready.compare, traceLen, traceWidth]
  have accepted := words_eq_of_poly _ _ checkWidth checkPoly
  refine ⟨⟨attempts, basisLen, basis, size, trace, gcd, raw⟩,
    ⟨attempt, live, cacheLen, cacheBound, cached, sizeRoom, traceLen, gcdLen, rawLen, invariant⟩, ?_⟩
  simpa only [accepted, decide_true, ite_true, TraceWrites.frame] using ran

#print axioms native_trace_check_accepts

end BulksketchBridge.RootTrace
