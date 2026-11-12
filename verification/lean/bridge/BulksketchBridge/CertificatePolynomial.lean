import BulksketchBridge.Certificate
import BulksketchBridge.SlicePolynomial
import BulksketchBridge.Algebra.WordLaws
import Mathlib.Algebra.BigOperators.Fin

namespace BulksketchBridge.Certificate

open Aeneas.Std Algebra.Gf64 RebuiltLfsr SliceKernels Polynomial
open scoped BigOperators

private theorem set_word (words : Slice U64) (index : Nat) (value : U64)
    (room : index < words.length) : (words.setAtNat index value)[index]! = value := by
  simpa only [Slice.getElem!_Nat_eq] using Slice.getElem!_Nat_setAtNat_eq words index value room

private theorem set_other (words : Slice U64) (index other : Nat) (value : U64)
    (different : index ≠ other) : (words.setAtNat index value)[other]! = words[other]! := by
  simpa only [Slice.getElem!_Nat_eq] using Slice.getElem!_Nat_setAtNat_ne words index other value different

private theorem descend_word (root : U64) (degree : Nat) (words : Slice U64)
    (room : degree < words.length) (index : Nat) (inside : index < words.length) :
    (descend root degree words)[index]! =
      if 0 < index ∧ index ≤ degree then words[index - 1]! ^^^ mulWord root words[index]!
      else words[index]! := by
  induction degree generalizing words with
  | zero => rw [descend, ite_eq_right (by omega)]
  | succ degree ih =>
    let updated := words.setAtNat (degree + 1) (words[degree]! ^^^ mulWord root words[degree + 1]!)
    have updatedLength : updated.length = words.length := Slice.setAtNat_length _ _ _
    change (descend root degree updated)[index]! = _
    rw [ih updated (by rw [updatedLength]; omega) (by rwa [updatedLength])]
    by_cases newest : index = degree + 1
    · subst index
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      simpa only [updated, Nat.add_sub_cancel] using
        set_word words (degree + 1) (words[degree]! ^^^ mulWord root words[degree + 1]!) room
    · have condition : (0 < index ∧ index ≤ degree.succ) ↔ (0 < index ∧ index ≤ degree) := by omega
      simp only [condition]
      have current : updated[index]! = words[index]! :=
        set_other _ _ _ _ (Ne.symm newest)
      by_cases written : 0 < index ∧ index ≤ degree
      · have previous : updated[index - 1]! = words[index - 1]! :=
          set_other _ _ _ _ (by omega)
        simp only [written, current, previous]
      · simp only [written, ite_false, current]

private theorem word_mul_zero (root : U64) : mulWord root 0#u64 = 0#u64 := by
  apply U64.bv_eq_imp_eq
  exact multiplyWord_zero root.bv

/-- One product step obeys the coefficient recurrence of multiplication by
`X + root`, including the first coefficient outside the old active degree. -/
theorem product_step_word (words : Slice U64) (root : U64) (degree index : Nat)
    (room : degree + 1 < words.length) (inside : index < words.length)
    (zeroTail : ∀ i, degree < i → i < words.length → words[i]! = 0#u64) :
    (productStep words root degree)[index]! =
      if index = 0 then mulWord root words[0]!
      else words[index - 1]! ^^^ mulWord root words[index]! := by
  let expanded := words.setAtNat (degree + 1) words[degree]!
  let shifted := descend root degree expanded
  have expandedLength : expanded.length = words.length := Slice.setAtNat_length _ _ _
  have shiftedLength : shifted.length = words.length := by simp only [shifted, descend_length, expandedLength]
  change (shifted.setAtNat 0 (mulWord root shifted[0]!))[index]! = _
  by_cases first : index = 0
  · subst index
    rw [set_word _ _ _ (by rw [shiftedLength]; omega)]
    have constant : shifted[0]! = words[0]! := by
      unfold shifted
      rw [descend_word _ _ _ (by rw [expandedLength]; omega) 0 (by rw [expandedLength]; omega),
        ite_eq_right (by omega)]
      exact set_other _ _ _ _ (by omega)
    simp only [constant, ite_true]
  · rw [set_other _ _ _ _ (Ne.symm first), ite_eq_right first]
    unfold shifted
    rw [descend_word _ _ _ (by rw [expandedLength]; omega) index (by rwa [expandedLength])]
    by_cases interior : index ≤ degree
    · rw [ite_eq_left (by omega)]
      have previous : expanded[index - 1]! = words[index - 1]! :=
        set_other _ _ _ _ (by omega)
      have current : expanded[index]! = words[index]! :=
        set_other _ _ _ _ (by omega)
      rw [previous, current]
    · rw [ite_eq_right (by omega), zeroTail index (by omega) inside, word_mul_zero]
      by_cases leading : index = degree + 1
      · subst index
        rw [show expanded[degree + 1]! = words[degree]! from set_word _ _ _ room]
        apply U64.bv_eq_imp_eq
        change words[degree]!.bv = words[degree]!.bv ^^^ (0 : BitVec 64)
        simp
      · have untouched : expanded[index]! = words[index]! :=
          set_other _ _ _ _ (Ne.symm leading)
        rw [untouched, zeroTail index (by omega) inside,
          zeroTail (index - 1) (by omega) (by omega)]
        rfl

/-- The spare coefficient and zero tail make the original fixed-buffer step
exact polynomial multiplication in the native GF64 quotient. -/
theorem product_step_polynomial (words : Slice U64) (root : U64) (degree : Nat)
    (room : degree + 1 < words.length)
    (zeroTail : ∀ i, degree < i → i < words.length → words[i]! = 0#u64) :
    slicePolynomial (productStep words root degree) =
      (X + C (toField root.bv)) * slicePolynomial words := by
  ext index
  rw [add_mul, coeff_add, coeff_C_mul, slicePolynomial_coeff, productStep_length]
  cases index with
  | zero =>
    have inside : 0 < words.length := by omega
    rw [coeff_X_mul_zero, zero_add, slicePolynomial_coeff, ite_eq_left inside, ite_eq_left inside,
      product_step_word words root degree 0 room inside zeroTail, ite_eq_left rfl]
    exact toField_mul root.bv words[0]!.bv
  | succ index =>
    rw [coeff_X_mul, slicePolynomial_coeff, slicePolynomial_coeff]
    by_cases inside : index + 1 < words.length
    · have previous : index < words.length := by omega
      rw [ite_eq_left inside, ite_eq_left inside, ite_eq_left previous,
        product_step_word words root degree (index + 1) room inside zeroTail,
        ite_eq_right (by omega : index + 1 ≠ 0)]
      change toField (words[index]!.bv ^^^ multiplyWord root.bv words[index + 1]!.bv) = _
      rw [toField_xor, toField_mul]
    · rw [ite_eq_right inside, ite_eq_right inside, mul_zero, add_zero]
      by_cases previous : index < words.length
      · rw [ite_eq_left previous, zeroTail index (by omega) previous]
        exact toField_zero.symm
      · rw [ite_eq_right previous]

/-- Every completed step advances the zero-padded degree by at most one and
accumulates the exact factors at the processed root positions. -/
theorem product_from_polynomial (roots words : Slice U64) (degree count : Nat)
    (range : degree + count ≤ roots.length) (room : roots.length < words.length)
    (zeroTail : ∀ i, degree < i → i < words.length → words[i]! = 0#u64) :
    slicePolynomial (productFrom roots words degree count) =
      slicePolynomial words * ∏ offset ∈ Finset.range count,
        (X + C (toField roots[degree + offset]!.bv)) := by
  induction count generalizing words degree with
  | zero => simp [productFrom]
  | succ count ih =>
    let next := productStep words roots[degree]! degree
    have nextLength : next.length = words.length := productStep_length _ _ _
    have nextTail (index : Nat) (after : degree + 1 < index) (inside : index < next.length) :
        next[index]! = 0#u64 := by
      rw [nextLength] at inside
      change (productStep words roots[degree]! degree)[index]! = _
      rw [product_step_word _ _ _ _ (by omega) inside zeroTail,
        ite_eq_right (by omega : index ≠ 0), zeroTail index (by omega) inside,
        zeroTail (index - 1) (by omega) (by omega), word_mul_zero]
      rfl
    change slicePolynomial (productFrom roots next (degree + 1) count) = _
    rw [ih next (degree + 1) (by omega) (by omega) nextTail]
    change (slicePolynomial (productStep words roots[degree]! degree) * _) = _
    rw [product_step_polynomial _ _ _ (by omega) zeroTail, Finset.prod_range_succ', Nat.add_zero]
    have shifted : (∏ offset ∈ Finset.range count, (X + C (toField roots[degree + 1 + offset]!.bv))) =
        ∏ offset ∈ Finset.range count, (X + C (toField roots[degree + (offset + 1)]!.bv)) := by
      apply Finset.prod_congr rfl
      intro offset _
      rw [show degree + 1 + offset = degree + (offset + 1) by omega]
    rw [shifted]
    ac_rfl

private theorem initial_tail (shape : Slice U64) (index : Nat) (positive : 0 < index)
    (inside : index < shape.length) : ((zeroWords shape).setAtNat 0 1#u64)[index]! = 0#u64 := by
  rw [set_other _ _ _ _ (by omega : 0 ≠ index), Slice.getElem!_Nat_eq]
  simp [zeroWords, inside]

private theorem initial_polynomial (shape : Slice U64) (nonempty : 0 < shape.length) :
    slicePolynomial ((zeroWords shape).setAtNat 0 1#u64) = 1 := by
  ext index
  rw [slicePolynomial_coeff, Slice.setAtNat_length, zero_length]
  by_cases first : index = 0
  · subst index
    rw [ite_eq_left nonempty, set_word _ _ _ (by simpa), coeff_one_zero]
    exact toField_one
  · rw [coeff_one, ite_eq_right first]
    by_cases inside : index < shape.length
    · rw [ite_eq_left inside, initial_tail shape index (by omega) inside]
      exact toField_zero
    · rw [ite_eq_right inside]

/-- Starting with the actual initialized unit buffer gives the monic product
over every root position. The product retains repeated roots if present. -/
theorem initialized_product_polynomial (roots shape : Slice U64) (room : roots.length < shape.length) :
    slicePolynomial (productFrom roots ((zeroWords shape).setAtNat 0 1#u64) 0 roots.length) =
      ∏ index ∈ Finset.range roots.length, (X + C (toField roots[index]!.bv)) := by
  rw [product_from_polynomial roots _ 0 roots.length (by omega) (by simpa using room)
    (fun index positive inside => initial_tail shape index positive (by simpa using inside)),
    initial_polynomial shape (by omega), one_mul]
  simp only [Nat.zero_add]

/-- Fixed-length slices are determined by their GF64 polynomial coefficients. -/
theorem slice_polynomial_eq_iff (left right : Slice U64) (sameLength : left.length = right.length) :
    slicePolynomial left = slicePolynomial right ↔ left = right := by
  constructor
  · intro equal
    apply Slice.ext_getElem sameLength
    intro index leftBound rightBound
    have coefficient := congrArg (fun p : Polynomial Field => p.coeff index) equal
    rw [slicePolynomial_coeff, slicePolynomial_coeff, ite_eq_left leftBound,
      ite_eq_left rightBound] at coefficient
    rw [Slice.Inhabited_getElem_eq_getElem! left index leftBound,
      Slice.Inhabited_getElem_eq_getElem! right index rightBound]
    apply U64.bv_eq_imp_eq
    exact toField_injective coefficient
  · rintro rfl
    rfl

private theorem product_from_length (roots words : Slice U64) (degree count : Nat) :
    (productFrom roots words degree count).length = words.length := by
  induction count generalizing words degree with
  | zero => rfl
  | succ count ih => simp only [productFrom, ih, productStep_length]

theorem rebuilt_product_eq_iff (factor roots shape : Slice U64)
    (room : roots.length < shape.length) (sameLength : shape.length = factor.length) :
    rebuiltProduct roots shape = factor ↔
      slicePolynomial factor = ∏ index ∈ Finset.range roots.length, (X + C (toField roots[index]!.bv)) := by
  have length : (rebuiltProduct roots shape).length = factor.length := by
    simp only [rebuiltProduct, product_from_length, Slice.setAtNat_length, zero_length, sameLength]
  rw [← slice_polynomial_eq_iff _ _ length, rebuiltProduct, initialized_product_polynomial roots shape room]
  constructor <;> intro equal <;> exact equal.symm

def ValidRoots (roots : Slice U64) : Prop :=
  ∀ index, index < roots.length → roots[index]! ≠ 0#u64 ∧
    ∀ earlier, earlier < index → roots[earlier]! ≠ roots[index]!

theorem valid_roots_iff (roots : Slice U64) : invalidFrom roots 0 roots.length = false ↔ ValidRoots roots := by
  rw [invalidFrom_false_iff]
  simp only [Nat.zero_add, invalidAt, not_or]
  constructor
  · intro valid index inside
    refine ⟨(valid index inside).1, ?_⟩
    intro earlier before equal
    apply (valid index inside).2
    rw [← equal]
    apply List.mem_iff_getElem.mpr
    have bounded : earlier < (roots.val.take index).length := by
      rw [List.length_take]
      change earlier < min index roots.length
      omega
    refine ⟨earlier, bounded, ?_⟩
    rw [List.getElem_take, Slice.getElem!_Nat_eq]
    exact List.Inhabited_getElem_eq_getElem! _ _ (by change earlier < roots.length; omega)
  · intro valid index inside
    refine ⟨(valid index inside).1, ?_⟩
    intro member
    obtain ⟨earlier, bounded, equal⟩ := List.mem_iff_getElem.mp member
    have before : earlier < index := by
      rw [List.length_take] at bounded
      omega
    apply (valid index inside).2 earlier before
    rw [List.getElem_take] at equal
    rw [Slice.getElem!_Nat_eq, ← List.Inhabited_getElem_eq_getElem! _ _ (by change earlier < roots.length; omega)]
    exact equal

private theorem expected_accepts (factor roots scratch : Slice U64)
    (capacity : roots.length + 1 = factor.length → invalidFrom roots 0 roots.length = false →
      factor.length ≤ scratch.length) :
    (expected factor roots scratch).1 = true ↔
      roots.length + 1 = factor.length ∧ ValidRoots roots ∧
        slicePolynomial factor = ∏ index ∈ Finset.range roots.length, (X + C (toField roots[index]!.bv)) := by
  rw [← valid_roots_iff roots]
  by_cases lengthValid : roots.length + 1 = factor.length
  · by_cases rootsValid : invalidFrom roots 0 roots.length = false
    · have shapeLength : (DenseCoefficient.prefixSlice scratch factor.length).length = factor.length := by
        rw [prefix_length, Nat.min_eq_left (capacity lengthValid rootsValid)]
      simpa [expected, lengthValid, rootsValid] using
        rebuilt_product_eq_iff factor roots (DenseCoefficient.prefixSlice scratch factor.length)
          (by rw [shapeLength]; omega) shapeLength
    · have invalid : invalidFrom roots 0 roots.length = true := Bool.eq_true_of_not_eq_false rootsValid
      simp [expected, lengthValid, invalid]
  · simp [expected, lengthValid]

/-- The original native certificate accepts precisely a nonzero distinct root
list whose monic product equals the supplied factor polynomial. -/
def ActualCertificateAcceptsRootPolynomial : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    NativeMul kernels → ∀ (factor roots scratch : Slice U64),
    roots.length + 1 ≤ Usize.max →
    (roots.length + 1 = factor.length → invalidFrom roots 0 roots.length = false →
      factor.length ≤ scratch.length) →
    ((∃ output, bulksketch.decode.deg34.certificate fieldDictionary kernels factor roots scratch =
      Result.ok (true, output)) ↔
      roots.length + 1 = factor.length ∧ ValidRoots roots ∧
        slicePolynomial factor = ∏ index ∈ Finset.range roots.length, (X + C (toField roots[index]!.bv)))

theorem certificate_accepts_root_polynomial : ActualCertificateAcceptsRootPolynomial := by
  intro K kernels mul factor roots scratch bounded capacity
  rw [certificate_refines kernels mul factor roots scratch bounded capacity]
  constructor
  · rintro ⟨output, normal⟩
    exact (expected_accepts factor roots scratch capacity).mp
      (congrArg Prod.fst (Result.ok_injective normal))
  · intro accepted
    refine ⟨(expected factor roots scratch).2, congrArg Result.ok ?_⟩
    exact Prod.ext ((expected_accepts factor roots scratch capacity).mpr accepted) rfl

end BulksketchBridge.Certificate
