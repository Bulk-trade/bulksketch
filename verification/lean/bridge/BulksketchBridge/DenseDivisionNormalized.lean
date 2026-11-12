import BulksketchBridge.DenseDivisionAlgebra
import BulksketchBridge.DirectTwoSpec

namespace BulksketchBridge.DenseDivision

open Aeneas.Std Algebra.Gf64 DenseCoefficient DenseNormalization SliceKernels Polynomial
open BmDiscrepancy
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096

private theorem first_rejected {α : Type} [Inhabited α] (predicate : α → Bool) (values : List α)
    (within : (values.takeWhile predicate).length < values.length) :
    predicate values[(values.takeWhile predicate).length]! = false := by
  induction values with
  | nil => simp at within
  | cons word rest ih =>
    cases tested : predicate word with
    | false =>
      simpa only [List.takeWhile, tested, Bool.false_eq_true, ite_false, List.length_nil,
        List.getElem!_cons_zero] using tested
    | true =>
      have shorter : (rest.takeWhile predicate).length < rest.length := by
        simpa only [List.takeWhile, tested, ite_true, List.length_cons, Nat.add_lt_add_iff_right] using within
      simpa only [List.takeWhile, tested, ite_true, List.length_cons, List.getElem!_cons_succ] using ih shorter

theorem normalized_last_nonzero (values : List U64) (positive : 0 < normalizedLength values) :
    values[normalizedLength values - 1]! ≠ 0#u64 := by
  let trailing := (values.reverse.takeWhile (· == 0#u64)).length
  have short : trailing < values.length := by
    change 0 < values.length - trailing at positive
    omega
  have index : normalizedLength values - 1 = values.length - 1 - trailing := by
    change values.length - trailing - 1 = _
    omega
  have inBounds : normalizedLength values - 1 < values.length := by omega
  have reverseIndex : trailing = values.length - 1 - (normalizedLength values - 1) := by omega
  have reverseRoom : trailing < values.reverse.length := by rw [List.length_reverse]; exact short
  have readReverse : values.reverse[trailing]! = values[normalizedLength values - 1]! := by
    rw [← List.Inhabited_getElem_eq_getElem! _ _ reverseRoom,
      ← List.Inhabited_getElem_eq_getElem! _ _ inBounds]
    have exactRead := List.getElem_eq_getElem_reverse inBounds
    simp only [← reverseIndex] at exactRead
    exact exactRead.symm
  have rejected := first_rejected (· == 0#u64) values.reverse reverseRoom
  change (values.reverse[trailing]! == 0#u64) = false at rejected
  rw [readReverse] at rejected
  intro zero
  simp [zero] at rejected

/-- The source normalized length has a nonzero final word when nonempty.
It never exceeds the exact span read by normalized_len. -/
theorem output_length_normal (words : Slice U64) (count : Nat) (room : count ≤ words.length) :
    let size := (DenseReducerSquare.outputLength words count).val
    size ≤ count ∧ (0 < size → (prefixSlice words size)[size - 1]! ≠ 0#u64) := by
  dsimp only
  rw [normalized_value _ _ room]
  let size := normalizedLength (words.val.take count)
  have sizeBound : size ≤ count := by
    have bounded := normalizedLength_le (words.val.take count)
    change size ≤ (words.val.take count).length at bounded
    exact bounded.trans (by simp [List.length_take])
  refine ⟨sizeBound, ?_⟩
  intro positive
  have last := normalized_last_nonzero (words.val.take count) positive
  have indexRoom : size - 1 < size := by omega
  have parentRoom : size - 1 < count := by omega
  change (words.val.take count)[size - 1]! ≠ 0#u64 at last
  change (prefixSlice words size)[size - 1]! ≠ _
  simpa only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val,
    List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt indexRoom,
    List.getElem?_take_of_lt parentRoom] using last

/-- Exact native width and normalized remainder admission for the next
Euclidean iteration. The final remainder length is strictly below the
nonempty divisor length, including when the dividend is already smaller. -/
theorem expected_remainder_normal (a b q rem : Slice U64) (raw : Slice Raw) (inverse : U64)
    (positive : 0 < b.length) (room : a.length + 1 ≤ rem.length) :
    let out := expectedDivRem a b q rem raw inverse
    out.1.2.val < b.length ∧
      (0 < out.1.2.val → (prefixSlice out.2.2.1 out.1.2.val)[out.1.2.val - 1]! ≠ 0#u64) := by
  let out := expectedDivRem a b q rem raw inverse
  let count := min (b.length - 1) a.length
  have size : out.1.2 = DenseReducerSquare.outputLength out.2.2.1 count := rfl
  obtain ⟨_, remWidth, _⟩ := expected_widths a b q rem raw inverse
  have bound : count ≤ out.2.2.1.length := by
    change count ≤ out.2.2.1.length
    rw [remWidth]
    unfold count
    omega
  have normal := output_length_normal out.2.2.1 count bound
  rw [← size] at normal
  have countBound : count < b.length := by
    unfold count
    exact (Nat.min_le_left _ _).trans_lt (by omega)
  exact ⟨normal.1.trans_lt countBound, normal.2⟩

noncomputable def divisorInverse (leading : U64) : U64 :=
  if leading = 1#u64 then 1#u64 else DirectTwo.inverseWord leading

theorem divisor_inverse_law (leading : U64) (nonzero : leading ≠ 0#u64) :
    toField (divisorInverse leading).bv * toField leading.bv = 1 := by
  unfold divisorInverse
  by_cases one : leading = 1#u64
  · rw [ite_eq_left one, one, show toField (1#u64 : U64).bv = 1 from toField_one, one_mul]
  · rw [ite_eq_right one]
    have fieldNonzero : toField leading.bv ≠ 0 := by
      intro zero
      apply nonzero
      apply U64.bv_eq_imp_eq
      exact wordFieldEquiv.injective (zero.trans toField_zero.symm)
    change wordFieldEquiv (wordFieldEquiv.symm (toField leading.bv)⁻¹) * toField leading.bv = 1
    rw [Equiv.apply_symm_apply, inv_mul_cancel₀ fieldNonzero]

end BulksketchBridge.DenseDivision
