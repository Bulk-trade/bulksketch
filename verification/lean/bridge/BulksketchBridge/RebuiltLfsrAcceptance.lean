import BulksketchBridge.RebuiltLfsr
import BulksketchBridge.RebuiltLocatorPolynomial
import BulksketchBridge.OddRecurrenceReconciliation

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

private theorem prefix_word (words : Slice U64) (count index : Nat) (bound : index < count) :
    (prefixSlice words count)[index]! = words[index]! := by
  simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val,
    List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt bound]

theorem rebuilt_lfsr_iff_direct : ActualRebuiltLfsrIffDirect := by
  intro K kernels linear square arithmetic nativeRecurrence roots odd coefficients expected seed
    distinct noZero room expectedRoom seedLen insert seedWords
  let shape := prefixSlice coefficients (roots.length + 1)
  let locator := locatorWords roots shape
  let squared := squareFrom locator 1
  have supportSize := rootSupport_card roots distinct
  have shapeSize : shape.length = roots.length + 1 := by
    simp [shape, Nat.min_eq_left (by omega : roots.length + 1 ≤ coefficients.length)]
  have squaredSize : squared.length = (rootSupport roots).card + 1 := by
    simp [squared, locator, locatorWords, Slice.setAtNat_length, shapeSize, supportSize]
  have squaredCoefficients (lag : Nat) (positive : 1 ≤ lag) (bounded : lag ≤ (rootSupport roots).card) :
      toField squared[lag]!.bv = ((rebuiltLocator (rootSupport roots)).coeff lag) ^ 2 := by
    exact squared_locator_word roots shape (by omega) distinct lag (by omega) (by omega)
  have seedRoom : seed.length ≤ odd.length := by omega
  have seedMatch : seed = prefixSlice odd seed.length ↔
      ∀ i, i < seed.length → toField odd[i]!.bv = oddSyndrome (rootSupport roots) i := by
    constructor
    · intro equal i active
      have word : seed[i]! = odd[i]! := (congrArg (fun s : Slice U64 => s[i]!) equal).trans
        (prefix_word odd seed.length i active)
      rw [← word]
      exact seedWords i active
    · intro agrees
      apply Slice.ext_getElem (by simp [Nat.min_eq_left seedRoom])
      intro i active bounded
      rw [Slice.Inhabited_getElem_eq_getElem! _ _ active,
        Slice.Inhabited_getElem_eq_getElem! _ _ bounded, prefix_word odd seed.length i active]
      have bits := toField_injective ((seedWords i active).trans (agrees i active).symm)
      exact UScalar.eq_of_val_eq (congrArg BitVec.toNat bits)
  have continuation (agrees : seed = prefixSlice odd seed.length) :
      ∃ accepted,
        kernels.odd_recurrence_matches odd squared = Result.ok accepted ∧
        (accepted = true ↔ ∀ i, i < odd.length →
          toField odd[i]!.bv = oddSyndrome (rootSupport roots) i) := by
    rw [nativeRecurrence]
    exact gf64_scalar_continuation_iff_direct kernels (rootSupport roots) odd squared
      arithmetic noZero squaredSize squaredCoefficients (by
        rw [supportSize, ← seedLen]
        exact seedMatch.mp agrees)
  obtain ⟨accepted, normal, selected⟩ :=
    rebuilt_lfsr_refines kernels linear square roots odd coefficients expected seed
      room expectedRoom seedLen insert (fun agrees => by
        obtain ⟨result, resultEq, _⟩ := continuation agrees
        exact ⟨result, resultEq⟩)
  refine ⟨accepted, _, _, normal, ?_⟩
  by_cases agrees : seed = prefixSlice odd seed.length
  · rw [ite_eq_left agrees] at selected
    obtain ⟨answer, answerEq, meaning⟩ := continuation agrees
    have identical : accepted = answer := by
      have same := selected.symm.trans answerEq
      exact Result.ok_injective same
    rw [identical, meaning]
  · rw [ite_eq_right agrees] at selected
    constructor
    · intro acceptedTrue
      simp [selected] at acceptedTrue
    · intro everyWord
      exact (agrees (seedMatch.mpr (fun i inside => everyWord i (inside.trans_le seedRoom)))).elim

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
