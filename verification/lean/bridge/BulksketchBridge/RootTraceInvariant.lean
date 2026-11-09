import BulksketchBridge.RootInvariantReborrow

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient RootTrace
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- A paid original Trace advances to GCD with the same live factor and
pending product. It also establishes the exact reborrow and GCD trace
polynomial, normalized trace window and strictly decreasing phase rank. -/
def ActualNativeTraceInvariant : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid finalMeter : WorkMeter) (capacity budget : Nat),
    RootTraversalInvariant locator roots workspace capacity budget → 3 ≤ roots.degree.val →
    roots.attempts.val + 1 ≤ Usize.max →
    bulksketch.decode.roots.charge meter (.Trace roots.degree) = .ok (.Ok (), paid) →
    (if roots.checked then finalMeter = paid
      else bulksketch.decode.roots.charge paid (.SplitCheck roots.degree) = .ok (.Ok (), finalMeter)) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    let before := buffersFor roots workspace
    cacheWellFormed roots before →
    CorrectTable before.modulus before.table roots.degree.val →
    BackendSquareLaw kernels before.modulus before.table roots.degree.val →
    TraceAgreement (activeFactor roots workspace) roots.splitter_seed roots.direction.val →
    ∃ writes : TraceWrites,
      let frame := writes.frame roots before true (.Ok (.Ok .Gcd)) finalMeter
      let after := frame.2.1
      let written := rebuild workspace roots frame.2.2.1
      let next := buffersFor after written
      let trace := prefixSlice next.trace after.trace_len.val
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Trace workspace meter =
        .ok (.Ok (.Ok .Gcd), after, written, id, finalMeter) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      activeFactor after written = activeFactor roots workspace ∧
      buffersFor after written = frame.2.2.1 ∧
      CorrectTable next.modulus next.table after.degree.val ∧
      cacheWellFormed after next ∧ after.attempts.val = roots.attempts.val + 1 ∧
      after.trace_len.val ≤ after.degree.val ∧ DenseGcd.Normal trace ∧
      traversalRank .Gcd after written < traversalRank .Trace roots workspace ∧
      ∀ point, (activeFactor after written).IsRoot point →
        ((slicePolynomial trace).IsRoot point ↔ traceBit roots.splitter_seed roots.direction.val point = 0)

theorem native_trace_invariant : ActualNativeTraceInvariant := by
  intro K kernels locator roots workspace meter paid finalMeter capacity budget invariant
    minimum counter charged splitCharge rawLaw squareLaw reduceLaw before cache table backend agreement
  have sized := invariant.buffers
  have degreeBudget : roots.degree.val ≤ budget := by
    have mass := invariant.mass
    have bounded := invariant.degreeBudget
    unfold factorDegreeMass at mass
    omega
  have positive : 0 < roots.degree.val := by omega
  obtain ⟨monic, exactDegree, split, simple, _⟩ := invariant.active positive
  have modWidth : before.modulus.length = roots.degree.val + 1 :=
    (gcd_buffers_of_budget roots workspace capacity budget sized (by omega) degreeBudget).2.1
  have monicWord : before.modulus[roots.degree.val]! = 1#u64 := by
    have coefficient : (slicePolynomial before.modulus).coeff roots.degree.val = 1 := by
      change (activeFactor roots workspace).coeff roots.degree.val = 1
      rw [← exactDegree, ← Polynomial.leadingCoeff]
      exact monic
    rw [slicePolynomial_coeff, ite_eq_left (by omega)] at coefficient
    apply U64.bv_eq_imp_eq
    exact toField_injective (coefficient.trans toField_one.symm)
  obtain ⟨writes, ran, correct, normalized, reborrow, meaning⟩ :=
    native_trace_dispatch kernels roots workspace meter paid finalMeter capacity budget sized
      minimum degreeBudget counter charged splitCharge rawLaw squareLaw reduceLaw cache monicWord
      table backend split simple agreement
  let frame := writes.frame roots before true (.Ok (.Ok .Gcd)) finalMeter
  let after := frame.2.1
  let written := rebuild workspace roots frame.2.2.1
  have restored : buffersFor after written = frame.2.2.1 := reborrow
  have rawWidth : frame.2.2.1.raw.length = workspace.raw.length := correct.2.2.2.2.2.2.2.2.1
  have preserved : RootTraversalInvariant locator after written capacity budget :=
    rebuild_preserves_traversal locator roots after workspace frame.2.2.1 capacity budget invariant
      rfl rfl rfl rfl rfl restored rfl rawWidth
  refine ⟨writes, ran, preserved, ?_, restored, ?_, ?_, correct.1, ?_, ?_, ?_, ?_⟩
  · change slicePolynomial (buffersFor after written).modulus = slicePolynomial before.modulus
    rw [restored]
    rfl
  · rw [restored]
    exact table
  · rw [restored]
    intro basis identity
    change some writes.basis = some basis at identity
    obtain rfl := Option.some.inj identity
    exact ⟨Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt correct.2.1), correct.2.2.2.1, correct.2.2.2.2.1⟩
  · have traceWidth : before.trace.length = roots.degree.val :=
      (gcd_buffers_of_budget roots workspace capacity budget sized (by omega) degreeBudget).2.2.1
    exact correct.2.2.2.2.2.1.trans
      (Nat.le_of_eq (correct.2.2.2.2.2.2.1.trans traceWidth))
  · rw [restored]
    exact normalized
  · apply traversal_rank_decreases
    exact Or.inr ⟨rfl, .trace _⟩
  · intro point present
    change (slicePolynomial (buffersFor after written).modulus).IsRoot point at present
    rw [restored] at present ⊢
    exact meaning point present

#print axioms native_trace_invariant

end BulksketchBridge.RootRun
