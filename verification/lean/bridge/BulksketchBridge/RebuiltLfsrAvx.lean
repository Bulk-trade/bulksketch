import BulksketchBridge.RebuiltLfsrAnyContinuation
import BulksketchBridge.AvxRecurrenceEntry
import BulksketchBridge.AvxLinearEntry

namespace BulksketchBridge.RebuiltLfsr

open Aeneas.Std AvxSquareRuntime AvxSquare Algebra.Gf64 Reconciliation
open bulksketch.backend.contract bulksketch.backend.portable
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (multiply_linear)

abbrev avxField := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

/-- Bind the proved original AVX locator-update entry and continuation
to the exact rebuilt verifier. The seed and square callback laws are
explicit, as are the masked load and store contracts. -/
def ActualRebuiltLfsrAvx : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (portable : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Portable F)
      {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    kernels.multiply_linear = multiply_linear load store portable avxField →
    kernels.odd_recurrence_matches =
      bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.odd_recurrence_matches
        load portable avxField →
    squaringLaw kernels →
    ∀ (roots odd coefficients expected seed : Slice U64),
      roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
      roots.length < coefficients.length →
      min roots.length odd.length ≤ expected.length →
      seed.length = min roots.length odd.length →
      kernels.insert_nonzero (zeroWords (DenseCoefficient.prefixSlice expected seed.length)) roots = .ok seed →
      (∀ i, i < seed.length → toField seed[i]!.bv = oddSyndrome (rootSupport roots) i) →
      ∃ accepted updatedCoefficients updatedExpected,
        bulksketch.decode.verify.rebuilt_lfsr avxField kernels roots odd coefficients expected =
          .ok (accepted, updatedCoefficients, updatedExpected) ∧
        (accepted = true ↔ ∀ i, i < odd.length →
          toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem rebuilt_lfsr_avx : ActualRebuiltLfsrAvx := by
  intro load store loadLaw storeLaw portable K kernels linearEq recurrenceEq square
  have linear : linearLaw kernels := by
    intro words root
    rw [linearEq]
    exact AvxMultiplyLinear.native_avx_linear_entry load store loadLaw storeLaw
      portable avxField 64#u32 words root (by simp [avxField, bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField, bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS])
  have recurrence : ContinuationLaw kernels := by
    intro odd locator positive
    rw [recurrenceEq]
    exact AvxRecurrence.native_avx_recurrence_entry_gf64 load loadLaw portable odd locator positive
  exact rebuilt_lfsr_any_continuation kernels linear square recurrence

#print axioms rebuilt_lfsr_avx

end BulksketchBridge.RebuiltLfsr
