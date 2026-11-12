import BulksketchBridge.DenseGcdAlgebra

namespace BulksketchBridge.DenseGcd

open Aeneas Aeneas.Std DenseCoefficient
open SliceKernels Algebra.Gf64 Polynomial
open bulksketch.backend.contract bulksketch.types
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

set_option maxRecDepth 4096

private theorem empty_poly (words : Slice U64) (empty : words.length = 0) :
    slicePolynomial words = 0 := by
  simp only [slicePolynomial, empty, Finset.range_zero, Finset.sum_empty]

private theorem normal_shape (words : Slice U64) (normal : Normal words) (positive : 0 < words.length) :
    slicePolynomial words ≠ 0 ∧ (slicePolynomial words).natDegree = words.length - 1 := by
  have upper : (slicePolynomial words).natDegree ≤ words.length - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i outside
    rw [slicePolynomial_coeff, ite_eq_right (by omega)]
  have lastNZ : (slicePolynomial words).coeff (words.length - 1) ≠ 0 := by
    rw [slicePolynomial_coeff, ite_eq_left (by omega)]
    intro zero
    exact normal positive (U64.bv_eq_imp_eq _ _ (toField_injective (zero.trans toField_zero.symm)))
  refine ⟨?_, natDegree_eq_of_le_of_coeff_ne_zero upper lastNZ⟩
  intro zero
  exact lastNZ (by rw [zero, coeff_zero])

/-- The source GCD's returned size is exact, including the zero case.
The final active left prefix is normalized by the loop contract, and
the native inverse scaling is the polynomial normalization, which
preserves its degree. -/
def ActualMonicGcdSize : Prop :=
  ∀ (division : DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (a b dst work : Slice U64) (raw : Slice RawProduct)
    (law : DivisionLaw division kernels) (meaning : DivisionMeaning division kernels)
    (inverse : BmTerminal.NativeInverse kernels) (scale : TimesXMod.ExactScaleXor kernels)
    (aNormal : Normal a) (bNormal : Normal b)
    (dstRoom : max a.length b.length ≤ dst.length)
    (workRoom : 4 * (max a.length b.length + 1) ≤ work.length)
    (rawRoom : 2 * (max a.length b.length + 1) ≤ raw.length)
    (size : Usize) (out outWork : Slice U64) (outRaw : Slice RawProduct)
    (returned : monic_gcd_into division dictionary kernels a b dst work raw = .ok (size, out, outWork, outRaw)),
    let p := gcd (slicePolynomial a) (slicePolynomial b)
    (size.val = 0 ↔ p = 0) ∧ (p ≠ 0 → size.val = p.natDegree + 1)

theorem native_gcd_size : ActualMonicGcdSize := by
  intro division K kernels a b dst work raw law meaning inverse scale aNormal bNormal dstRoom workRoom rawRoom
    size out outWork outRaw returned
  let limit := max a.length b.length
  let width := limit + 1
  let state := startState width a b work raw
  have aRoom : a.length < width := Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have bRoom : b.length < width := Nat.lt_succ_of_le (Nat.le_max_right _ _)
  have rawWidth : width ≤ raw.length := by change 2 * width ≤ raw.length at rawRoom; omega
  have ready := start_ready a b work raw width workRoom rawWidth aRoom bRoom aNormal bNormal
  have enough : state.rightLen.val ≤ b.length := by simp only [state, startState, Slice.len_val, Nat.le_refl]
  obtain ⟨final, modeled, _, finalReady, finalZero⟩ :=
    run_refines division kernels law width b.length state ready enough
  have pEq := run_preserves_gcd division kernels law meaning width b.length state final ready enough modeled
  have zeroPoly : slicePolynomial final.rightWords = 0 := by
    apply empty_poly
    rw [finalReady.rightLength, finalZero]
    rfl
  have left := start_left a b work raw width workRoom aRoom
  have right := start_right a b work raw width workRoom bRoom
  change state.leftWords = a at left
  change state.rightWords = b at right
  rw [left, right, zeroPoly, gcd_zero_right] at pEq
  have finalExpected : expected division kernels a b dst work raw =
      .ok (final.leftLen, destination dst limit final, restoreWork work width final, final.raw) := by
    simp only [expected, state, width, limit] at modeled ⊢
    rw [modeled, bind_ok]
  obtain ⟨frame, exactNative, exactExpected⟩ :=
    monic_gcd_refines division kernels a b dst work raw law inverse scale aNormal bNormal dstRoom workRoom rawRoom
  have sizeEq : size = final.leftLen :=
    congrArg Prod.fst
      ((Result.ok_injective (returned.symm.trans exactNative)).trans
        (Result.ok_injective (exactExpected.symm.trans finalExpected)))
  dsimp only
  rw [pEq, sizeEq, ← finalReady.leftLength, normalize_eq_zero, natDegree_normalize]
  refine ⟨⟨empty_poly _, ?_⟩, ?_⟩
  · intro zero
    by_contra notEmpty
    exact (normal_shape final.leftWords finalReady.leftNormal (Nat.pos_of_ne_zero notEmpty)).1 zero
  · intro nonzero
    have positive : 0 < final.leftWords.length := by
      apply Nat.pos_of_ne_zero
      exact fun zero => nonzero (normalize_eq_zero.mpr (empty_poly _ zero))
    rw [(normal_shape _ finalReady.leftNormal positive).2]
    omega

end BulksketchBridge.DenseGcd
