import BulksketchBridge.RootGcdFrame
import BulksketchBridge.RootReborrow
import BulksketchBridge.RootDivideArena
import BulksketchBridge.NativeRootRun
import BulksketchBridge.RootTraceProgress

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient SliceKernels RebuiltLfsr BmEntry
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2100000

private theorem outcome_fields (roots : Roots) (buffers : FactorWork) (size : Usize) :
    let after := (outcome roots buffers size).2
    after.degree = roots.degree ∧ after.gcd_len = size ∧ after.gcd_degree.val = size.val - 1 := by
  have fits : size.val - 1 ≤ Usize.max := (Nat.sub_le ..).trans (by scalar_tac)
  have deg : (degree size).val = size.val - 1 := ClosedLeafAdvance.word_val _ fits
  dsimp only
  by_cases proper : 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val
  · simp only [outcome, proper, ite_true, deg, true_and]
  · cases affine : roots.affine <;>
      simp only [outcome, proper, ite_false, affine, Bool.false_eq_true, ite_true, deg, true_and]

/-- A paid original GCD returns the exact normalized polynomial and
reborrows its native workspace at the next stage. The proper branch
supplies the precise input shape required by native factor division. -/
def ActualNativeGcdReborrow : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter)
    (capacity budget : Nat),
    BudgetBuffers workspace capacity budget → 2 ≤ roots.degree.val → roots.degree.val ≤ budget →
    roots.trace_len.val ≤ roots.degree.val →
    bulksketch.decode.roots.charge meter (.Gcd roots.degree) = .ok (.Ok (), paid) →
    DenseDivRem.MulWordLaw kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    DenseMul.reduceAgrees kernels → BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    let buffers := buffersFor roots workspace
    let trace := prefixSlice buffers.trace roots.trace_len.val
    let factor := slicePolynomial buffers.modulus
    let tracePoly := slicePolynomial trace
    DenseGcd.Normal buffers.modulus → DenseGcd.Normal trace →
    factor.Monic → factor.natDegree = roots.degree.val →
    (roots.affine = true → 0 < roots.affine_rank.val ∧ roots.affine_rank.val ≤ 64 ∧ buffers.basis.directions.isSome) →
    (roots.affine = false → roots.direction.val < 64) →
    ∃ (size : Usize) (result work : Slice U64) (raw : Slice RawProduct),
      let next := outcome roots buffers size
      let updated := { buffers with gcd := result, work, raw }
      let written := rebuild workspace roots updated
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Gcd workspace meter =
        .ok (next.1, next.2, written, id, paid) ∧
      buffersFor next.2 written = updated ∧ raw.length = buffers.raw.length ∧
      size.val = (gcd factor tracePoly).natDegree + 1 ∧
      slicePolynomial (prefixSlice result size.val) = gcd factor tracePoly ∧
      (Proper roots size →
        next.1 = .Ok (.Ok .FactorDivision) ∧
        RootDivide.ProperGcdFrame next.2 (buffersFor next.2 written) tracePoly) ∧
      (roots.affine = false → ¬ Proper roots size → factor.Splits → factor.roots.Nodup →
        TraceAgreement factor roots.splitter_seed roots.direction.val →
        (∀ point, factor.IsRoot point → (tracePoly.IsRoot point ↔
          traceBit roots.splitter_seed roots.direction.val point = 0)) →
        next.1 = .Ok (.Ok .Trace) ∧ next.2.direction.val < 64 ∧
        TraceAgreement factor roots.splitter_seed next.2.direction.val)

theorem native_gcd_reborrow : ActualNativeGcdReborrow := by
  intro K kernels roots workspace meter paid capacity budget sized degreeMin degreeBound traceBound charged
    mul rawLaw reduce inverse scale buffers trace factor tracePoly aNormal bNormal monic degreeEq affine direction
  obtain ⟨⟨polyRoom, tableRoom⟩, modulusWidth, traceWidth, gcdWidth, workWidth, rawWidth⟩ :=
    gcd_buffers_of_budget roots workspace capacity budget sized degreeMin degreeBound
  change buffers.modulus.length = roots.degree.val + 1 at modulusWidth
  change buffers.trace.length = roots.degree.val at traceWidth
  change buffers.gcd.length = roots.degree.val + 1 at gcdWidth
  change 4 * (roots.degree.val + 2) ≤ buffers.work.length at workWidth
  change 2 * (roots.degree.val + 2) ≤ buffers.raw.length at rawWidth
  have traceWidthBound : trace.length ≤ roots.degree.val := by rw [prefix_length, traceWidth]; omega
  have limit : max buffers.modulus.length trace.length = roots.degree.val + 1 := by
    rw [modulusWidth, max_eq_left (by omega)]
  have gcdFit : max buffers.modulus.length trace.length ≤ buffers.gcd.length := by rw [limit, gcdWidth]
  have workFit : 4 * (max buffers.modulus.length trace.length + 1) ≤ buffers.work.length := by rw [limit]; omega
  have rawFit : 2 * (max buffers.modulus.length trace.length + 1) ≤ buffers.raw.length := by rw [limit]; omega
  obtain ⟨law, meaning⟩ := DenseDivRem.original_gcd_laws kernels mul rawLaw reduce inverse
  obtain ⟨size, result, work, raw, normal, _, _, exactGcd⟩ :=
    DenseGcd.monic_gcd_meaning nativeDivRem kernels buffers.modulus trace buffers.gcd buffers.work buffers.raw
      law meaning inverse scale aNormal bNormal gcdFit workFit rawFit
  have gNonzero : gcd factor tracePoly ≠ 0 := fun zero => monic.ne_zero ((gcd_eq_zero_iff _ _).mp zero).1
  have sizeExact : size.val = (gcd factor tracePoly).natDegree + 1 :=
    (DenseGcd.native_gcd_size nativeDivRem kernels buffers.modulus trace buffers.gcd buffers.work buffers.raw
      law meaning inverse scale aNormal bNormal gcdFit workFit rawFit size result work raw normal).2 gNonzero
  obtain ⟨gcdLength, workLength, rawLength⟩ := DenseGcd.native_gcd_widths nativeDivRem kernels law inverse scale
    buffers.modulus trace buffers.gcd buffers.work buffers.raw aNormal bNormal gcdFit workFit rawFit size result work raw normal
  have admission : AfterGcdReady roots buffers size :=
    ⟨by omega, fun _ h => ⟨(affine h).1, fun _ => ⟨(affine h).2.2, (affine h).2.1⟩⟩,
      fun _ h => by have := direction h; rw [U32.max_eq]; omega⟩
  have ran := run_gcd_paid nativeCalls nativeDivRem kernels roots workspace meter paid polyRoom tableRoom
    traceBound charged size result work raw normal admission
  let after := (outcome roots buffers size).2
  let updated := { buffers with gcd := result, work, raw }
  let written := rebuild workspace roots updated
  obtain ⟨afterDegree, gcdLen, gcdDegree⟩ := outcome_fields roots buffers size
  have reborrow : buffersFor after written = updated := by
    have sameDegree : after.degree = roots.degree := afterDegree
    have borrow : buffersFor after written = buffersFor roots written := by unfold buffersFor; rw [sameDegree]
    rw [borrow]
    apply reborrow_factor_work roots workspace updated ⟨polyRoom, tableRoom⟩
    · exact modulusWidth
    · exact traceWidth
    · exact gcdLength.trans gcdWidth
    · change work.length = _
      rw [workLength]
      change (tail (tail (tail workspace.polynomials (roots.degree.val + 1)) roots.degree.val)
        (roots.degree.val + 1)).length = _
      simp only [tail_length]
    · change (prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val)).length = _
      rw [prefix_length, Nat.min_eq_left tableRoom]
  refine ⟨size, result, work, raw, ran, reborrow, rawLength, sizeExact, exactGcd, ?_, ?_⟩
  · intro proper
    have branch : (outcome roots buffers size).1 = .Ok (.Ok .FactorDivision) := by
      unfold outcome
      rw [ite_eq_left (show 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val from proper)]
    have properDegree : 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val := proper
    refine ⟨branch, ?_⟩
    change RootDivide.ProperGcdFrame after (buffersFor after written) tracePoly
    rw [reborrow]
    refine ⟨monic, ?_, ?_, ?_, ?_, ?_⟩
    · rw [afterDegree]
      exact degreeEq
    · change slicePolynomial (prefixSlice result after.gcd_len.val) = gcd factor tracePoly
      rw [gcdLen]
      exact exactGcd
    · rw [gcdLen, gcdDegree]
      omega
    · rw [gcdDegree]
      change size.val - 1 = (gcd factor tracePoly).natDegree
      omega
    · rw [afterDegree, gcdDegree]
      exact properDegree
  · intro notAffine nonproper split simple agrees classifies
    obtain ⟨stage, _, nextBound, retained⟩ :=
      trace_gcd_retry roots buffers size factor tracePoly notAffine monic split simple
        (by omega) degreeEq sizeExact nonproper agrees classifies
    exact ⟨stage, nextBound, retained⟩

#print axioms native_gcd_reborrow

end BulksketchBridge.RootRun
