import BulksketchBridge.RebuiltLfsrAnyContinuation

namespace BulksketchBridge.RebuiltLfsr

open Aeneas.Std Algebra.Gf64 DenseCoefficient Reconciliation
open bulksketch.backend.contract

/-- The original rebuilt verifier accepts precisely a row encoded by the
given distinct nonzero support. The seed callback is related to the odd
syndromes, and the continuation uses the proved original scalar default. -/
def ActualRebuiltLfsrIffDirect : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    linearLaw kernels → squaringLaw kernels → OddRecurrence.CorrectArithmetic kernels →
    kernels.odd_recurrence_matches = BulkKernels.odd_recurrence_matches.default kernels →
    ∀ (roots odd coefficients expected seed : Slice U64),
      roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
      roots.length < coefficients.length →
      min roots.length odd.length ≤ expected.length →
      seed.length = min roots.length odd.length →
      kernels.insert_nonzero (zeroWords (prefixSlice expected seed.length)) roots = Result.ok seed →
      (∀ i, i < seed.length → toField seed[i]!.bv = oddSyndrome (rootSupport roots) i) →
      ∃ accepted updatedCoefficients updatedExpected,
        bulksketch.decode.verify.rebuilt_lfsr
          bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels roots odd coefficients expected =
          Result.ok (accepted, updatedCoefficients, updatedExpected) ∧
        (accepted = true ↔ ∀ i, i < odd.length →
          toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem rebuilt_lfsr_iff_direct : ActualRebuiltLfsrIffDirect := by
  intro K kernels linear square arithmetic nativeRecurrence
  have law : ContinuationLaw kernels := by
    intro odd locator nonempty
    rw [nativeRecurrence]
    exact OddRecurrence.default_refines kernels odd locator arithmetic nonempty
  exact rebuilt_lfsr_any_continuation kernels linear square law

/-- The original default multiply-linear callback supplies the word-level
law used by the rebuilt verifier when multiplication is the proved GF64 body. -/
theorem linear_default_matches {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (nativeMul : ∀ a b, kernels.ArithmeticInst.mul a b =
      bulksketch.field.gf64.mul bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField a b)
    (words : Slice U64) (root : U64) :
    BulkKernels.multiply_linear.default kernels words root = Result.ok (linearStep words root) := by
  obtain ⟨output, normal, length, frame⟩ := SliceKernels.multiply_linear_refines K kernels nativeMul words root
  rw [normal]
  apply congrArg Result.ok
  apply Slice.ext_getElem (length.trans (linear_length words root).symm)
  intro index outBound modelBound
  have inside : index < words.length := by omega
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ outBound, frame index inside,
    Slice.Inhabited_getElem_eq_getElem! _ _ modelBound, linear_word words root index inside]


end BulksketchBridge.RebuiltLfsr
