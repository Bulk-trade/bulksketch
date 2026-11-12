import BulksketchBridge.RebuiltSquareLoop
import BulksketchBridge.ReconciliationLfsr
import BulksketchBridge.Algebra.WordLaws
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace BulksketchBridge.RebuiltLfsr

open Aeneas Aeneas.Std Algebra.Gf64 DenseCoefficient SliceKernels SliceKernelChallenges
open Polynomial
open scoped BigOperators

private theorem prefix_word (words : Slice U64) (stop index : Nat) (inside : index < stop) :
    (prefixSlice words stop)[index]! = words[index]! := by
  simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD,
    List.getElem?_take_of_lt inside]

theorem linear_word (words : Slice U64) (root : U64) (index : Nat)
    (inside : index < words.length) : (linearStep words root)[index]! = coefficientAfter words root index := by
  simp only [linearStep, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ index (by simpa using inside), List.getElem_ofFn]

private theorem coefficient_zero (words : Slice U64) (root : U64) (index : Nat)
    (positive : 0 < index) (here : words[index]! = 0#u64)
    (prior : words[index - 1]! = 0#u64) : coefficientAfter words root index = 0#u64 := by
  simp only [coefficientAfter, ite_eq_right (by omega : index ≠ 0), here, prior]
  apply U64.bv_eq_imp_eq
  change (0 : BitVec 64) ^^^ multiplyWord 0 root.bv = 0
  rw [zero_multiplyWord]
  simp

/-- Multiplying only the active prefix and its spare word produces the same
full frame as multiplying the entire zero-padded buffer. -/
private theorem locator_step_frame (words : Slice U64) (root : U64) (used index : Nat)
    (room : used + 2 ≤ words.length) (inside : index < words.length)
    (zeroTail : ∀ i, used < i → i < words.length → words[i]! = 0#u64) :
    (locatorStep words root (used + 2))[index]! = coefficientAfter words root index := by
  have prefixLen : (prefixSlice words (used + 2)).length = used + 2 := by
    simp [Nat.min_eq_left room]
  have replacementLen : (linearStep (prefixSlice words (used + 2)) root).val.length = used + 2 := by
    change (linearStep (prefixSlice words (used + 2)) root).length = used + 2
    rw [linear_length, prefixLen]
  unfold locatorStep restorePrefix
  rw [Slice.getElem!_Nat_eq, Slice.from_val]
  by_cases active : index < used + 2
  · rw [List.getElem!_setSlice!_middle _ _ _ _ (by
      rw [replacementLen]
      simpa only [Nat.zero_le, Nat.sub_zero, true_and] using And.intro active inside), Nat.sub_zero,
      ← Slice.getElem!_Nat_eq, linear_word _ _ _ (by omega)]
    unfold coefficientAfter
    rw [prefix_word _ _ _ active, prefix_word _ _ _ (by omega)]
  · rw [List.getElem!_setSlice!_suffix _ _ _ _ (by rw [replacementLen]; omega), ← Slice.getElem!_Nat_eq,
      zeroTail index (by omega) inside]
    exact (coefficient_zero words root index (by omega) (zeroTail index (by omega) inside)
      (zeroTail (index - 1) (by omega) (by omega))).symm

private theorem locator_from_product (roots words : Slice U64) (used count : Nat)
    (range : used + count ≤ roots.length) (room : roots.length < words.length)
    (zeroTail : ∀ i, used < i → i < words.length → words[i]! = 0#u64) :
    slicePolynomial (locatorFrom roots words used count) =
      slicePolynomial words * ∏ offset ∈ Finset.range count,
        (1 + C (toField roots[used + offset]!.bv) * X) := by
  induction count generalizing words used with
  | zero => simp [locatorFrom]
  | succ count ih =>
    let next := locatorStep words roots[used]! (used + 2)
    have nextLen : next.length = words.length := locator_step_length _ _ _
    have prefixRoom : used + 2 ≤ words.length := by omega
    have frame := fun i inside => locator_step_frame words roots[used]! used i prefixRoom inside zeroTail
    have nextTail (i : Nat) (after : used + 1 < i) (inside : i < next.length) : next[i]! = 0#u64 := by
      rw [nextLen] at inside
      rw [frame i inside]
      exact coefficient_zero words roots[used]! i (by omega)
        (zeroTail i (by omega) inside) (zeroTail (i - 1) (by omega) (by omega))
    have exactProduct := SliceKernels.exact_product words next roots[used]! nextLen frame
      (fun _ => zeroTail (words.length - 1) (by omega) (by omega))
    change slicePolynomial (locatorFrom roots next (used + 1) count) = _
    rw [ih next (used + 1) (by omega) (by omega) nextTail, exactProduct,
      Finset.prod_range_succ', Nat.add_zero]
    have shifted : (∏ offset ∈ Finset.range count,
        (1 + C (toField roots[used + 1 + offset]!.bv) * X)) =
        ∏ offset ∈ Finset.range count, (1 + C (toField roots[used + (offset + 1)]!.bv) * X) := by
      apply Finset.prod_congr rfl
      intro offset _
      rw [show used + 1 + offset = used + (offset + 1) by omega]
    rw [shifted]
    ac_rfl

private theorem init_tail (shape : Slice U64) (index : Nat) (positive : 0 < index)
    (inside : index < shape.length) : ((zeroWords shape).setAtNat 0 1#u64)[index]! = 0#u64 := by
  rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega : 0 ≠ index)]
  simp [zeroWords, inside]

private theorem init_polynomial (shape : Slice U64) (nonempty : 0 < shape.length) :
    slicePolynomial ((zeroWords shape).setAtNat 0 1#u64) = 1 := by
  ext index
  rw [slicePolynomial_coeff, Slice.setAtNat_length, zero_length]
  by_cases first : index = 0
  · subst index
    rw [ite_eq_left nonempty, Slice.getElem!_Nat_eq,
      Slice.getElem!_Nat_setAtNat_eq _ _ _ (by simpa), coeff_one_zero]
    exact toField_one
  · rw [coeff_one, ite_eq_right first]
    by_cases inside : index < shape.length
    · rw [ite_eq_left inside, init_tail shape index (by omega) inside]
      exact toField_zero
    · rw [ite_eq_right inside]

private theorem rootWord_injective : Function.Injective (fun word : U64 => toField word.bv) := by
  intro left right equal
  apply U64.bv_eq_imp_eq
  exact toField_injective equal

noncomputable def rootSupport (roots : Slice U64) : Finset Field := by
  classical
  exact (roots.val.map fun word => toField word.bv).toFinset

theorem rootSupport_card (roots : Slice U64) (distinct : roots.val.Nodup) :
    (rootSupport roots).card = roots.length := by
  classical
  simpa only [rootSupport, List.length_map, Slice.length] using
    List.toFinset_card_of_nodup (List.Nodup.map rootWord_injective distinct)

/-- For a distinct root list the active locator is the product over its support. -/
theorem locator_words_product (roots shape : Slice U64) (room : roots.length < shape.length)
    (distinct : roots.val.Nodup) :
    slicePolynomial (locatorWords roots shape) = Reconciliation.rebuiltLocator (rootSupport roots) := by
  classical
  let initial := (zeroWords shape).setAtNat 0 1#u64
  have initialLength : initial.length = shape.length := by
    simp only [initial, Slice.setAtNat_length, zero_length]
  change slicePolynomial (locatorFrom roots initial 0 roots.length) = _
  rw [locator_from_product roots initial 0 roots.length (by omega) (by omega) (fun index positive inside =>
      init_tail shape index positive (by omega)), init_polynomial shape (by omega), one_mul]
  simp only [Nat.zero_add, Reconciliation.rebuiltLocator, rootSupport]
  rw [List.prod_toFinset _ (distinct.map rootWord_injective), List.map_map,
    ← List.ofFn_getElem_eq_map, List.prod_ofFn,
    ← Fin.prod_univ_eq_prod_range (fun index => 1 + C (toField roots[index]!.bv) * X) roots.length]
  apply Finset.prod_congr rfl
  intro index _
  simp only [Function.comp_apply, Slice.getElem!_Nat_eq,
    List.Inhabited_getElem_eq_getElem! roots.val index.val index.isLt]

/-- Squaring the active locator tail gives the coefficients used by the
continuation sum at every positive lag. -/
theorem squared_locator_word (roots shape : Slice U64) (room : roots.length < shape.length)
    (distinct : roots.val.Nodup) (lag : Nat) (positive : 0 < lag) (inside : lag < shape.length) :
    toField (squareFrom (locatorWords roots shape) 1)[lag]!.bv =
      ((Reconciliation.rebuiltLocator (rootSupport roots)).coeff lag) ^ 2 := by
  have length : (locatorWords roots shape).length = shape.length := by
    simp [locatorWords, Slice.setAtNat_length]
  have inLocator : lag < (locatorWords roots shape).length := by rwa [length]
  rw [square_word _ _ _ inLocator, ite_eq_left (by omega : 1 ≤ lag),
    ← locator_words_product roots shape room distinct, slicePolynomial_coeff, ite_eq_left inLocator]
  exact toField_square _

end BulksketchBridge.RebuiltLfsr
