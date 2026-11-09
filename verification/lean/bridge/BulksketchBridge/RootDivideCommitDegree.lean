import BulksketchBridge.RootDivideDegree
import BulksketchBridge.RootPendingBudget

namespace BulksketchBridge.RootDivide

open Aeneas.Std RootRun DenseCoefficient BmEntry
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial (exact_divide_into)

set_option maxRecDepth 4096
set_option maxHeartbeats 1700000

/-- On the actual successful native divide branch, the committed active GCD
    and pending quotient preserve the parent degree mass. The quotient is
    nonconstant, as required by the next pending-slot admission. -/
def ActualNativeCommittedDegreeMass : Prop :=
  ∀ (division : DenseDivisionRuntime.DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter paid finalMeter : WorkMeter) (length start stop : Usize),
    DenseDivision.RefinesModel division kernels →
    NativeDivideReady roots buffers → ProperDivideShape roots buffers →
    (nativeCall roots buffers).1 = some length →
    StageCharge.chargeResult meter (divideCost roots.degree) = (.Ok (), paid) →
    StageCharge.chargeResult paid (assemblyCost roots.degree) = (.Ok (), finalMeter) →
    Usize.checked_mul roots.pending roots.stride = some start →
    Usize.checked_add start length = some stop →
    CommitReady roots buffers factors stack (nativeCall roots buffers).2.1 length start stop →
    let call := nativeCall roots buffers
    let output := committed roots buffers factors stack finalMeter length start call.2.1 call.2.2.1 call.2.2.2
    Roots.divide (exact_divide_into division) DenseGcd.dictionary kernels roots buffers factors stack meter = .ok output ∧
    factorDegreeMass output.2.1 output.2.2.2.2.2.1 = factorDegreeMass roots stack ∧
    0 < length.val - 1

theorem native_committed_degree_mass : ActualNativeCommittedDegreeMass := by
  intro division K kernels roots buffers factors stack meter paid finalMeter length start stop
    law ready shape candidate charged assembly startOk endOk commit
  let call := nativeCall roots buffers
  have admission (length' start' stop' : Usize)
      (otherCandidate : call.1 = some length')
      (otherStart : Usize.checked_mul roots.pending roots.stride = some start')
      (otherStop : Usize.checked_add start' length' = some stop') :
      CommitReady roots buffers factors stack call.2.1 length' start' stop' := by
    have sameLength := Option.some.inj (candidate.symm.trans otherCandidate)
    have sameStart := Option.some.inj (startOk.symm.trans otherStart)
    subst length'
    subst start'
    have sameStop := Option.some.inj (endOk.symm.trans otherStop)
    subst stop'
    exact commit
  obtain ⟨positive, _, _, degrees, _⟩ := native_call_degree roots buffers ready shape length candidate
  refine ⟨?_, committed_degree_mass roots buffers factors stack finalMeter length start
    call.2.1 call.2.2.1 call.2.2.2 commit.slotRoom degrees, positive⟩
  rw [native_divide_refines division kernels roots buffers factors stack meter law ready admission]
  have modeled :
      exactDivisionModel DenseGcd.dictionary kernels buffers.modulus
        (prefixSlice buffers.gcd roots.gcd_len.val)
        (prefixSlice buffers.work (roots.degree.val + 2))
        (tail buffers.work (roots.degree.val + 2)) buffers.raw =
        .ok (some length, call.2.1, call.2.2.1, call.2.2.2) := by
    change Result.ok call = _
    apply congrArg Result.ok
    have selected : call.1 = some length := candidate
    rw [← selected]
  simp only [expected, charged, modeled, bind_ok]
  dsimp! only
  simp only [assembly, startOk, endOk]
  rfl

#print axioms native_committed_degree_mass

end BulksketchBridge.RootDivide
