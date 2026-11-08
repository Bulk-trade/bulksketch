import BulksketchBridge.DenseGcd
import BulksketchBridge.SlicePolynomial
import Mathlib.Algebra.Polynomial.FieldDivision

namespace BulksketchBridge.DenseGcd

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr SliceKernels Algebra.Gf64 Polynomial
open bulksketch.backend.contract bulksketch.types
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- The division result supplies the usual quotient/remainder identity on
exactly the returned normalized prefixes. This composes with the separate
frame and strict descent contract used by the original loop. -/
def DivisionMeaning (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ (left right quotient remainder : Slice U64) (raw : Slice RawProduct)
    (qLen remLen : Usize) (qOut remOut : Slice U64) (rawOut : Slice RawProduct),
    Normal left → Normal right → 0 < right.length →
    left.length + 1 ≤ quotient.length → left.length + 1 ≤ remainder.length →
    left.length + 1 ≤ raw.length →
    division dictionary kernels left right quotient remainder raw = .ok ((qLen, remLen), qOut, remOut, rawOut) →
    slicePolynomial left = slicePolynomial (prefixSlice qOut qLen.val) * slicePolynomial right +
      slicePolynomial (prefixSlice remOut remLen.val)

private theorem gcd_decomposition (left right quotient remainder : Field[X])
    (equation : left = quotient * right + remainder) :
    gcd left right = gcd right remainder := by
  calc
    _ = gcd remainder right := by
      apply gcd_eq_of_dvd_sub_left
      refine ⟨quotient, ?_⟩
      rw [equation, add_sub_cancel_right, mul_comm]
    _ = _ := gcd_comm _ _

theorem run_preserves_gcd (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (law : DivisionLaw division kernels) (meaning : DivisionMeaning division kernels)
    (width fuel : Nat) (state final : State) (ready : Ready width state) (enough : state.rightLen.val ≤ fuel)
    (returned : run division kernels fuel state = .ok final) :
    gcd (slicePolynomial state.leftWords) (slicePolynomial state.rightWords) =
      gcd (slicePolynomial final.leftWords) (slicePolynomial final.rightWords) := by
  induction fuel generalizing state with
  | zero =>
    have zero : state.rightLen = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa using enough
    simp only [run, zero, ite_true] at returned
    have same := Result.ok_injective returned
    subst final
    rfl
  | succ fuel ih =>
    by_cases zero : state.rightLen = 0#usize
    · simp only [run, zero, ite_true] at returned
      have same := Result.ok_injective returned
      subst final
      rfl
    · have nonzero : 0 < state.rightLen.val := by
        apply Nat.pos_of_ne_zero
        intro h
        apply zero
        apply UScalar.eq_of_val_eq
        simpa using h
      have positive : 0 < state.rightWords.length := ready.rightLength.symm ▸ nonzero
      have qRoom : state.leftWords.length + 1 ≤ state.quotient.length := by
        rw [ready.leftLength, ready.quotientWidth]; exact ready.leftRoom
      have remRoom : state.leftWords.length + 1 ≤ state.remainder.length := by
        rw [ready.leftLength, ready.remainderWidth]; exact ready.leftRoom
      have rawRoom : state.leftWords.length + 1 ≤ state.raw.length := by
        rw [ready.leftLength]; exact ready.leftRoom.trans_le ready.rawRoom
      obtain ⟨qLen, remLen, qOut, remOut, rawOut, call, qWidth, remWidth, rawWidth, decrease, normalized⟩ :=
        law state.leftWords state.rightWords state.quotient state.remainder state.raw
          ready.leftNormal ready.rightNormal positive qRoom remRoom rawRoom
      let next := state.advance ((qLen, remLen), qOut, remOut, rawOut)
      have nextReady := ready.advance qLen remLen qOut remOut rawOut qWidth remWidth rawWidth decrease normalized
      have nextFuel : next.rightLen.val ≤ fuel := by
        rw [ready.rightLength] at decrease
        change remLen.val ≤ fuel
        omega
      have equation := meaning state.leftWords state.rightWords state.quotient state.remainder state.raw
        qLen remLen qOut remOut rawOut ready.leftNormal ready.rightNormal positive qRoom remRoom rawRoom call
      have preserved : gcd (slicePolynomial state.leftWords) (slicePolynomial state.rightWords) =
          gcd (slicePolynomial next.leftWords) (slicePolynomial next.rightWords) :=
        gcd_decomposition _ _ _ _ equation
      simp only [run, zero, ite_false, call, bind_ok] at returned
      exact preserved.trans (ih next nextReady nextFuel returned)

private theorem empty_polynomial (words : Slice U64) (empty : words.length = 0) :
    slicePolynomial words = 0 := by
  simp only [slicePolynomial, empty, Finset.range_zero, Finset.sum_empty]

private theorem scaled_length (words : Slice U64) (scale : U64) :
    (scaledPrefix words scale).length = words.length := by simp [scaledPrefix, Slice.length]

private theorem scaled_polynomial (words : Slice U64) (scale : U64) :
    slicePolynomial (scaledPrefix words scale) = C (toField scale.bv) * slicePolynomial words := by
  ext i
  rw [coeff_C_mul, slicePolynomial_coeff, slicePolynomial_coeff, scaled_length]
  by_cases active : i < words.length
  · rw [ite_eq_left active, ite_eq_left active]
    have scaledRoom : i < (scaledPrefix words scale).val.length := by
      change i < (scaledPrefix words scale).length
      rwa [scaled_length]
    rw [Slice.getElem!_Nat_eq (scaledPrefix words scale),
      ← List.Inhabited_getElem_eq_getElem! _ _ scaledRoom]
    simp only [scaledPrefix, Slice.from_val, List.getElem_map]
    rw [List.Inhabited_getElem_eq_getElem! _ _ active, ← Slice.getElem!_Nat_eq]
    exact toField_mul _ _
  · simp only [active, ite_false, mul_zero]

private theorem leading_coeff (words : Slice U64) (normal : Normal words) (positive : 0 < words.length) :
    (slicePolynomial words).leadingCoeff = toField words[words.length - 1]!.bv := by
  have bounded : (slicePolynomial words).natDegree ≤ words.length - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n beyond
    rw [slicePolynomial_coeff, ite_eq_right (by omega)]
  have atLast : (slicePolynomial words).coeff (words.length - 1) = toField words[words.length - 1]!.bv := by
    rw [slicePolynomial_coeff, ite_eq_left (by omega)]
  have nonzero : (slicePolynomial words).coeff (words.length - 1) ≠ 0 := by
    rw [atLast]
    intro zero
    have bitEq := wordFieldEquiv.injective (zero.trans toField_zero.symm)
    exact normal positive (U64.bv_eq_imp_eq _ _ bitEq)
  unfold leadingCoeff
  rw [natDegree_eq_of_le_of_coeff_ne_zero bounded nonzero, atLast]

private theorem gcd_words_length {width : Nat} {state : State} (ready : Ready width state) :
    (gcdWords state).length = state.leftLen.val := by
  unfold gcdWords
  split
  · exact ready.leftLength
  · dsimp only
    split
    · exact ready.leftLength
    · rw [scaled_length, ready.leftLength]

private theorem gcd_words_polynomial {width : Nat} {state : State} (ready : Ready width state) :
    slicePolynomial (gcdWords state) = normalize (slicePolynomial state.leftWords) := by
  by_cases zero : state.leftLen = 0#usize
  · have empty : state.leftWords.length = 0 := by rw [ready.leftLength, zero]; rfl
    simp only [gcdWords, zero, ite_true, empty_polynomial _ empty, normalize_zero]
  · have positive : 0 < state.leftLen.val := by
      apply Nat.pos_of_ne_zero
      intro h
      apply zero
      apply UScalar.eq_of_val_eq
      simpa using h
    have nonempty : 0 < state.leftWords.length := by rwa [ready.leftLength]
    have lead := leading_coeff state.leftWords ready.leftNormal nonempty
    have word : state.leftWords[state.leftWords.length - 1]! = state.left[state.leftLen.val - 1]! := by
      have bound := ready.leftRoom.le.trans (by rw [ready.leftWidth] : width ≤ state.left.length)
      rw [ready.leftLength]
      change (prefixSlice state.left state.leftLen.val)[state.leftLen.val - 1]! = _
      simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val]
      simpa only [List.slice, List.drop_zero, Nat.sub_zero, Nat.zero_add] using
        List.getElem!_slice 0 state.leftLen.val (state.leftLen.val - 1) state.left.val ⟨bound, by omega⟩
    rw [word] at lead
    by_cases one : state.left[state.leftLen.val - 1]! = 1#u64
    · have monic : (slicePolynomial state.leftWords).Monic := by
        unfold Monic
        rw [lead, one]
        exact toField_one
      simp only [gcdWords, zero, ite_false, one, ite_true, monic.normalize_eq_self]
    · have leadWordNZ : state.left[state.leftLen.val - 1]! ≠ 0#u64 := by
        rw [← word]
        exact ready.leftNormal nonempty
      have leadingNZ : (slicePolynomial state.leftWords).leadingCoeff ≠ 0 := by
        rw [lead]
        intro fieldZero
        exact leadWordNZ (U64.bv_eq_imp_eq _ _ (wordFieldEquiv.injective (fieldZero.trans toField_zero.symm)))
      simp only [gcdWords, zero, ite_false, one, scaled_polynomial]
      rw [normalize_apply, Polynomial.coe_normUnit, CommGroupWithZero.coe_normUnit Field leadingNZ, lead, mul_comm (slicePolynomial state.leftWords)]
      exact congrArg (fun c => C c * slicePolynomial state.leftWords) (wordFieldEquiv.apply_symm_apply _)

private theorem destination_polynomial {width : Nat} {state : State} (ready : Ready width state)
    (dst : Slice U64) (limit : Nat) (room : limit ≤ dst.length) (bound : state.leftLen.val ≤ limit) :
    slicePolynomial (prefixSlice (destination dst limit state) state.leftLen.val) =
      normalize (slicePolynomial state.leftWords) := by
  have exactPrefix : prefixSlice (destination dst limit state) state.leftLen.val = gcdWords state := by
    by_cases zero : state.leftLen = 0#usize
    · apply Slice.ext
      simp only [gcdWords, zero, ite_true, State.leftWords, prefixSlice, Slice.from_val]
      change (destination dst limit state).val.take 0 = state.left.val.take 0
      simp only [List.take_zero]
    · simp only [destination, zero, ite_false]
      have gcdLen := gcd_words_length ready
      rw [← gcdLen]
      exact prefix_restored _ _ (by rw [restore_length, gcdLen]; exact bound.trans room)
  rw [exactPrefix, gcd_words_polynomial ready]

/-- The exact original stage returns the canonical monic GCD of the
two normalized input slices. The witness still contains the exact
work and raw frame from ActualMonicGcd. -/
def ActualMonicGcdMeaning : Prop :=
  ∀ (division : DivRem) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (a b dst work : Slice U64) (raw : Slice RawProduct),
    DivisionLaw division kernels → DivisionMeaning division kernels →
    BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    Normal a → Normal b →
    max a.length b.length ≤ dst.length →
    4 * (max a.length b.length + 1) ≤ work.length →
    2 * (max a.length b.length + 1) ≤ raw.length →
    ∃ (size : Usize) (out outWork : Slice U64) (outRaw : Slice RawProduct),
      monic_gcd_into division dictionary kernels a b dst work raw = .ok (size, out, outWork, outRaw) ∧
      expected division kernels a b dst work raw = .ok (size, out, outWork, outRaw) ∧
      size.val ≤ max a.length b.length ∧
      slicePolynomial (prefixSlice out size.val) = gcd (slicePolynomial a) (slicePolynomial b)

theorem monic_gcd_meaning : ActualMonicGcdMeaning := by
  intro division K kernels a b dst work raw law meaning inverse scale aNormal bNormal dstRoom workRoom rawRoom
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
  have preserve := run_preserves_gcd division kernels law meaning width b.length state final ready enough modeled
  have zeroPoly : slicePolynomial final.rightWords = 0 := by
    apply empty_polynomial
    rw [finalReady.rightLength, finalZero]
    rfl
  have left := start_left a b work raw width workRoom aRoom
  have right := start_right a b work raw width workRoom bRoom
  change state.leftWords = a at left
  change state.rightWords = b at right
  rw [left, right, zeroPoly, gcd_zero_right] at preserve
  have resultEq : expected division kernels a b dst work raw =
      .ok (final.leftLen, destination dst limit final, restoreWork work width final, final.raw) := by
    simp only [expected, state, width, limit] at modeled ⊢
    rw [modeled, bind_ok]
  obtain ⟨out, native, expectedEq⟩ :=
    monic_gcd_refines division kernels a b dst work raw law inverse scale aNormal bNormal dstRoom workRoom rawRoom
  have same := Result.ok_injective (expectedEq.symm.trans resultEq)
  rw [same] at native
  have bound : final.leftLen.val ≤ limit := by have room := finalReady.leftRoom; omega
  refine ⟨final.leftLen, destination dst limit final, restoreWork work width final, final.raw, native, resultEq, bound, ?_⟩
  exact (destination_polynomial finalReady dst limit dstRoom bound).trans preserve.symm

end BulksketchBridge.DenseGcd
