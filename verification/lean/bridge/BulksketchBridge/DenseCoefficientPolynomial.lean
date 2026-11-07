import BulksketchBridge.DenseCoefficient
import BulksketchBridge.SlicePolynomial

namespace BulksketchBridge.DenseCoefficient

open Aeneas.Std Polynomial BulksketchBridge.Algebra.Gf64
open SliceKernels DenseNormalization

/-- The active window uses the same polynomial interpretation as the slice
kernel proofs. Taking a prefix excludes inactive scratch words. -/
def prefixSlice (words : Slice U64) (count : Nat) : Slice U64 :=
  Slice.from (words.val.take count) (by
    rw [List.length_take]
    exact (Nat.min_le_right _ _).trans words.length_ineq)

theorem prefix_coeff (words : Slice U64) (count index : Nat)
    (bounded : count ≤ words.length) :
    (slicePolynomial (prefixSlice words count)).coeff index =
      if index < count then toField words[index]!.bv else 0 := by
  have actualLength : (prefixSlice words count).length = count := by
    simp only [prefixSlice, Slice.length, Slice.from_val, List.length_take,
      Nat.min_eq_left bounded]
  rw [slicePolynomial_coeff, actualLength]
  by_cases active : index < count
  · simp only [active, ite_true, prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val,
      List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt active]
  · simp only [active, ite_false]

private theorem takeWhile_accepts {α : Type} [Inhabited α] (predicate : α → Bool)
    (values : List α) (index : Nat) (bounded : index < (values.takeWhile predicate).length) :
    predicate values[index]! = true := by
  induction values generalizing index with
  | nil => simp at bounded
  | cons first rest ih =>
    by_cases accepted : predicate first = true
    · cases index with
      | zero => simpa using accepted
      | succ index =>
        simp only [List.getElem!_cons_succ]
        apply ih
        simp [List.takeWhile, accepted] at bounded
        omega
    · simp [List.takeWhile, accepted] at bounded

private theorem normalized_suffix_zero (values : List U64) (index : Nat)
    (after : normalizedLength values ≤ index) (bounded : index < values.length) :
    values[index]! = 0#u64 := by
  have trailing : values.length - 1 - index <
      (values.reverse.takeWhile (· == 0#u64)).length := by
    unfold normalizedLength at after
    omega
  have reverseBound : values.length - 1 - index < values.reverse.length := by
    rw [List.length_reverse]
    omega
  have reverseRead : values.reverse[values.length - 1 - index]! = values[index]! := by
    rw [← List.Inhabited_getElem_eq_getElem! _ _ reverseBound,
      ← List.Inhabited_getElem_eq_getElem! _ _ bounded]
    exact (List.getElem_eq_getElem_reverse bounded).symm
  have zero := takeWhile_accepts (· == 0#u64) values.reverse
    (values.length - 1 - index) trailing
  rw [reverseRead] at zero
  exact beq_iff_eq.mp zero

theorem normalized_prefix_polynomial (words : Slice U64) (count : Nat)
    (bounded : count ≤ words.length) :
    slicePolynomial (prefixSlice words (normalizedLength (words.val.take count))) =
      slicePolynomial (prefixSlice words count) := by
  have normalizedBound : normalizedLength (words.val.take count) ≤ count := by
    simpa only [List.length_take, Nat.min_eq_left bounded] using
      normalizedLength_le (words.val.take count)
  ext index
  rw [prefix_coeff words _ index (normalizedBound.trans bounded), prefix_coeff words count index bounded]
  by_cases kept : index < normalizedLength (words.val.take count)
  · simp only [kept, show index < count by omega, ite_true]
  · rw [ite_eq_right kept]
    by_cases active : index < count
    · have zero := normalized_suffix_zero (words.val.take count) index (by omega)
        (by simpa only [List.length_take, Nat.min_eq_left bounded] using active)
      have wordZero : words[index]! = 0#u64 := by
        simpa only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
          List.getElem?_take_of_lt active] using zero
      rw [ite_eq_left active, wordZero]
      exact toField_zero.symm
    · rw [ite_eq_right active]

private theorem active_polynomial_update (original result : Slice U64) (length index : Nat)
    (value : U64) (lengthBound : length ≤ original.length) (indexBound : index < original.length)
    (sameLength : result.length = original.length)
    (frame : ∀ slot, slot < original.length →
      result[slot]! = expectedCoefficient original length index value slot) :
    slicePolynomial (prefixSlice result (activeSize length index)) =
      slicePolynomial (prefixSlice original length) + monomial index (toField value.bv) := by
  have sizeBound : activeSize length index ≤ result.length := by
    rw [sameLength]
    exact max_le lengthBound (by omega)
  have containsOld : length ≤ activeSize length index := Nat.le_max_left _ _
  have containsIndex : index < activeSize length index :=
    Nat.lt_of_succ_le (Nat.le_max_right _ _)
  ext slot
  rw [coeff_add, coeff_monomial, prefix_coeff result _ slot sizeBound,
    prefix_coeff original _ slot lengthBound]
  by_cases selected : slot = index
  · subst slot
    rw [ite_eq_left containsIndex, frame index indexBound]
    simp only [expectedCoefficient, ite_true, UScalar.bv_xor]
    by_cases earlier : index < length
    · simp only [earlier, ite_true]
      exact toField_xor _ _
    · simp only [earlier, ite_false]
      rw [toField_xor, show toField (0#u64).bv = 0 from toField_zero]
  · by_cases earlier : slot < length
    · have active : slot < activeSize length index := by omega
      rw [ite_eq_left active, frame slot (by omega)]
      simp [expectedCoefficient, selected, Ne.symm selected, earlier, Nat.not_le_of_lt earlier]
    · by_cases active : slot < activeSize length index
      · rw [ite_eq_left active, frame slot (by omega)]
        simp only [expectedCoefficient, selected, Ne.symm selected, earlier, active,
          show length ≤ slot by omega, and_true, ite_false, ite_true, add_zero]
        exact toField_zero
      · simp [active, earlier, Ne.symm selected]

/-- The edited monomial is added in the existing GF64 quotient, and removing
the zero suffix preserves the polynomial. -/
def XorCoefficientPolynomialRefines : Prop :=
  ∀ (Backend : Type) (kernels : bulksketch.backend.contract.BulkKernels Backend bulksketch.field.Gf64)
    (original : Slice U64) (length index : Usize) (value : U64),
    length.val ≤ original.length → index.val < original.length →
    ∃ normalized : Usize, ∃ result : Slice U64,
      bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.xor_coefficient
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels original length index value =
          .ok (normalized, result) ∧ result.length = original.length ∧
      slicePolynomial (prefixSlice result (activeSize length.val index.val)) =
        slicePolynomial (prefixSlice original length.val) + monomial index.val (toField value.bv) ∧
      slicePolynomial (prefixSlice result normalized.val) =
        slicePolynomial (prefixSlice result (activeSize length.val index.val))

theorem xor_coefficient_polynomial_refines : XorCoefficientPolynomialRefines := by
  intro Backend kernels original length index value lengthBound indexBound
  have source := xor_coefficient_refines
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels original length index value
  dsimp only at source
  rw [ite_eq_left ⟨lengthBound, indexBound⟩] at source
  obtain ⟨normalized, result, normal, sameLength, frame, normalizedValue⟩ := source
  refine ⟨normalized, result, normal, sameLength,
    active_polynomial_update original result length.val index.val value lengthBound indexBound sameLength frame, ?_⟩
  rw [normalizedValue]
  apply normalized_prefix_polynomial
  rw [sameLength]
  exact max_le lengthBound (by omega)

end BulksketchBridge.DenseCoefficient
