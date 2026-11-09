import BulksketchBridge.AffineMultipleDependentWitness
import BulksketchBridge.DenseDivisionNormalized

namespace BulksketchBridge.AffineMultiple

open Aeneas.Std Algebra.Gf64 Polynomial DenseReducerAlgebra ClosedLeaf DenseCoefficient RebuiltLfsr BmEntry
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

/-- Store a checked row or witness window as scalar products of its input. -/
def writeScaledRow (matrix : Slice U64) (width row start stop : Nat)
    (sourceWindow : Slice U64) (inverse : U64) : Slice U64 :=
  let offset := row * width
  matrix.setSlice! (offset + start)
    (MutableZip.mapFrom (region matrix (offset + start) (offset + stop))
      sourceWindow (scaleWord inverse) 0).val

@[simp] theorem write_scaled_length (matrix : Slice U64) (width row start stop : Nat)
    (sourceWindow : Slice U64) (inverse : U64) :
    (writeScaledRow matrix width row start stop sourceWindow inverse).length = matrix.length := by
  simp only [writeScaledRow, Slice.setSlice!_length]

private theorem matrix_window_size (matrix : Slice U64) (width row start stop : Nat)
    (fits : (row + 1) * width ≤ matrix.length) (stopRoom : stop ≤ width) :
    (region matrix (row * width + start) (row * width + stop)).length = stop - start := by
  have rowEnd : (row + 1) * width = row * width + width := by rw [Nat.add_mul, Nat.one_mul]
  rw [ClosedLeaf.region_length _ _ _ (by omega)]
  omega

/-- The full normalized matrix row is the scalar product of the full
source when both are zero outside their written windows. -/
theorem written_row_value (matrix source sourceWindow : Slice U64) (width row start stop : Nat)
    (inverse : U64) (fits : (row + 1) * width ≤ matrix.length) (stopRoom : stop ≤ width)
    (sourceAt : ∀ i < stop - start, sourceWindow[i]! = source[start + i]!)
    (oldZero : ∀ i < width, i < start ∨ stop ≤ i → (matrixRow matrix width row)[i]! = 0#u64)
    (sourceZero : ∀ i < width, i < start ∨ stop ≤ i → source[i]! = 0#u64)
    (index : Nat) (inside : index < width) :
    toField (matrixRow (writeScaledRow matrix width row start stop sourceWindow inverse) width row)[index]!.bv =
      toField source[index]!.bv * toField inverse.bv := by
  let patch := MutableZip.mapFrom (region matrix (row * width + start) (row * width + stop))
    sourceWindow (scaleWord inverse) 0
  have patchWidth : patch.length = stop - start := by
    rw [show patch = MutableZip.mapFrom (region matrix (row * width + start) (row * width + stop))
      sourceWindow (scaleWord inverse) 0 from rfl, MutableZip.mapFrom_length, matrix_window_size _ _ _ _ _ fits stopRoom]
  have newFits : (row + 1) * width ≤ (writeScaledRow matrix width row start stop sourceWindow inverse).length := by
    simpa only [write_scaled_length] using fits
  rw [matrix_row_word _ _ _ _ newFits inside]
  change toField (matrix.setSlice! (row * width + start) patch.val)[row * width + index]!.bv = _
  by_cases outside : index < start ∨ stop ≤ index
  · have unchanged : (matrix.setSlice! (row * width + start) patch.val)[row * width + index]! =
        matrix[row * width + index]! := by
      simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
      apply List.getElem!_setSlice!_same
      change row * width + index < row * width + start ∨
        row * width + start + patch.length ≤ row * width + index
      rw [patchWidth]
      omega
    rw [unchanged, ← matrix_row_word _ _ _ _ fits inside, oldZero index inside outside, sourceZero index inside outside]
    change toField 0 = toField 0 * toField inverse.bv
    rw [toField_zero, zero_mul]
  · have relative : index - start < stop - start := by omega
    have address : row * width + index - (row * width + start) = index - start := by omega
    have actual : (matrix.setSlice! (row * width + start) patch.val)[row * width + index]! =
        patch[index - start]! := by
      simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
      rw [List.getElem!_setSlice!_middle _ _ _ _ (by
        change row * width + start ≤ row * width + index ∧
          row * width + index - (row * width + start) < patch.length ∧
          row * width + index < matrix.length
        rw [address, patchWidth]
        have rowEnd : (row + 1) * width = row * width + width := by rw [Nat.add_mul, Nat.one_mul]
        omega), address]
    rw [actual]
    have mapped : patch[index - start]! = scaleWord inverse
        (region matrix (row * width + start) (row * width + stop))[index - start]!
        sourceWindow[index - start]! := by
      unfold patch
      rw [MutableZip.mapFrom_word _ _ _ _ _ (by rw [matrix_window_size _ _ _ _ _ fits stopRoom]; exact relative),
        ite_eq_left (Nat.zero_le _)]
    rw [mapped, sourceAt _ relative, show start + (index - start) = index by omega]
    change toField (multiplyWord source[index]!.bv inverse.bv) = _
    rw [toField_mul]

/-- Writing one row cannot touch any other original matrix row. -/
theorem written_other_row (matrix : Slice U64) (width row other start stop : Nat)
    (sourceWindow : Slice U64) (inverse : U64)
    (fits : (row + 1) * width ≤ matrix.length) (otherFits : (other + 1) * width ≤ matrix.length)
    (ordered : start ≤ stop) (stopRoom : stop ≤ width) (different : other ≠ row) :
    matrixRow (writeScaledRow matrix width row start stop sourceWindow inverse) width other =
      matrixRow matrix width other := by
  have newFits : (other + 1) * width ≤ (writeScaledRow matrix width row start stop sourceWindow inverse).length := by
    simpa only [write_scaled_length] using otherFits
  have outWidth := matrix_row_length (writeScaledRow matrix width row start stop sourceWindow inverse) width other newFits
  have oldWidth := matrix_row_length matrix width other otherFits
  apply Slice.ext_getElem (outWidth.trans oldWidth.symm)
  intro index left right
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ left, Slice.Inhabited_getElem_eq_getElem! _ _ right]
  have inside : index < width := by rwa [oldWidth] at right
  rw [matrix_row_word _ _ _ _ newFits inside, matrix_row_word _ _ _ _ otherFits inside]
  unfold writeScaledRow
  dsimp only
  simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
  apply List.getElem!_setSlice!_same
  change other * width + index < row * width + start ∨
    row * width + start + (MutableZip.mapFrom (region matrix (row * width + start) (row * width + stop))
      sourceWindow (scaleWord inverse) 0).length ≤ other * width + index
  rw [MutableZip.mapFrom_length, matrix_window_size _ _ _ _ _ fits stopRoom]
  by_cases earlier : other < row
  · left
    have within : (other + 1) * width ≤ row * width := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at within
    omega
  · right
    have later : (row + 1) * width ≤ other * width := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at later
    omega

private theorem weighted_scale {R : Type} [CommSemiring R] (cast : Field →+* R) (weights : Nat → R)
    (source written : Slice U64) (inverse : U64) (width : written.length = source.length)
    (words : ∀ i < source.length,
      toField written[i]!.bv = toField source[i]!.bv * toField inverse.bv) :
    weightedValue cast weights written = cast (toField inverse.bv) * weightedValue cast weights source := by
  unfold weightedValue
  rw [width, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i member
  rw [words i (Finset.mem_range.mp member), map_mul]
  ac_rfl

/-- Installing a selected pivot preserves the actual row and witness
quotient invariant for the next column. The new diagonal becomes one;
the older rows are untouched. -/
theorem store_pivot_witness_rows (modulus : Slice U64) (degree column pivot : Nat)
    (rows witnesses vector witness : Slice U64)
    (table : WitnessRows modulus degree column rows witnesses)
    (state : ColumnWitness modulus degree column vector witness)
    (columnActive : column < degree) (pivotActive : pivot < degree)
    (below : ∀ i < pivot, vector[i]! = 0#u64) (nonzero : vector[pivot]! ≠ 0#u64) :
    WitnessRows modulus degree (column + 1)
      (normalizedRows degree pivot rows vector (DenseDivision.divisorInverse vector[pivot]!))
      (normalizedWitnesses (degree + 1) pivot column witnesses witness
        (DenseDivision.divisorInverse vector[pivot]!)) := by
  let inverse := DenseDivision.divisorInverse vector[pivot]!
  let nextRows := writeScaledRow rows degree pivot pivot degree (tail vector pivot) inverse
  let nextWitnesses := writeScaledRow witnesses (degree + 1) pivot 0 (column + 1)
    (prefixSlice witness (column + 1)) inverse
  have exactRows : normalizedRows degree pivot rows vector inverse = nextRows := by
    simp only [normalizedRows, nextRows, writeScaledRow, Nat.add_mul, Nat.one_mul]
  have exactWitnesses : normalizedWitnesses (degree + 1) pivot column witnesses witness inverse = nextWitnesses := by
    simp only [normalizedWitnesses, nextWitnesses, writeScaledRow, Nat.add_zero, Nat.add_assoc]
  change WitnessRows modulus degree (column + 1)
    (normalizedRows degree pivot rows vector inverse)
    (normalizedWitnesses (degree + 1) pivot column witnesses witness inverse)
  rw [exactRows, exactWitnesses]
  have rowsLength : nextRows.length = rows.length := write_scaled_length ..
  have witnessesLength : nextWitnesses.length = witnesses.length := write_scaled_length ..
  have rowFits : ∀ row < degree, (row + 1) * degree ≤ rows.length := fun row active =>
    (Nat.mul_le_mul_right degree (Nat.succ_le_of_lt active)).trans table.rowsRoom
  have witnessFits : ∀ row < degree, (row + 1) * (degree + 1) ≤ witnesses.length := fun row active =>
    (Nat.mul_le_mul_right (degree + 1) (Nat.succ_le_of_lt active)).trans table.witnessesRoom
  have rowValue : ∀ i < degree,
      toField (matrixRow nextRows degree pivot)[i]!.bv = toField vector[i]!.bv * toField inverse.bv := by
    intro i inside
    apply written_row_value rows vector (tail vector pivot) degree pivot pivot degree inverse
      (rowFits pivot pivotActive) (Nat.le_refl _) (fun _ _ => tail_word _ _ _) _ _ i inside
    · intro j within outside
      exact table.rowBelow pivot pivotActive j (by omega)
    · intro j within outside
      exact below j (by omega)
  have witnessValue : ∀ i < degree + 1,
      toField (matrixRow nextWitnesses (degree + 1) pivot)[i]!.bv =
        toField witness[i]!.bv * toField inverse.bv := by
    intro i inside
    apply written_row_value witnesses witness (prefixSlice witness (column + 1))
      (degree + 1) pivot 0 (column + 1) inverse (witnessFits pivot pivotActive)
      (Nat.succ_le_succ table.columnRoom) _ _ _ i inside
    · intro j inner
      rw [Nat.sub_zero] at inner
      rw [Nat.zero_add]
      exact prefix_word _ _ _ inner
    · intro j within outside
      exact table.witnessAfter pivot pivotActive j within (by omega)
    · intro j within outside
      exact state.future j within (by omega)
  have unchangedRows (row : Nat) (active : row < degree) (different : row ≠ pivot) :
      matrixRow nextRows degree row = matrixRow rows degree row :=
    written_other_row rows degree pivot row pivot degree (tail vector pivot) inverse
      (rowFits pivot pivotActive) (rowFits row active) (Nat.le_of_lt pivotActive) (Nat.le_refl _) different
  have unchangedWitnesses (row : Nat) (active : row < degree) (different : row ≠ pivot) :
      matrixRow nextWitnesses (degree + 1) row = matrixRow witnesses (degree + 1) row :=
    written_other_row witnesses (degree + 1) pivot row 0 (column + 1) (prefixSlice witness (column + 1)) inverse
      (witnessFits pivot pivotActive) (witnessFits row active) (Nat.zero_le _) (Nat.succ_le_succ table.columnRoom) different
  refine ⟨Nat.succ_le_of_lt columnActive, by rw [rowsLength]; exact table.rowsRoom,
    by rw [witnessesLength]; exact table.witnessesRoom, ?_, ?_, ?_, ?_⟩
  · intro row active i earlier
    by_cases equal : row = pivot
    · subst row
      apply word_eq_zero
      rw [rowValue i (by omega), below i earlier]
      change toField 0 * _ = 0
      rw [toField_zero, zero_mul]
    · rw [unchangedRows row active equal]
      exact table.rowBelow row active i earlier
  · intro row active i inside future
    by_cases equal : row = pivot
    · subst row
      apply word_eq_zero
      rw [witnessValue i inside, state.future i inside (by omega)]
      change toField 0 * _ = 0
      rw [toField_zero, zero_mul]
    · rw [unchangedWitnesses row active equal]
      exact table.witnessAfter row active i inside (by omega)
  · intro row active
    by_cases equal : row = pivot
    · subst row
      have rowWidth : (matrixRow nextRows degree pivot).length = vector.length := by
        rw [matrix_row_length _ _ _ (by rw [rowsLength]; exact rowFits pivot pivotActive), state.vectorWidth]
      have witnessWidth : (matrixRow nextWitnesses (degree + 1) pivot).length = witness.length := by
        rw [matrix_row_length _ _ _ (by rw [witnessesLength]; exact witnessFits pivot pivotActive), state.witnessWidth]
      have scaledVector := weighted_scale ((residue modulus).comp C) (fun index => residueX modulus ^ index)
        vector (matrixRow nextRows degree pivot) inverse rowWidth (by
          intro i inside; exact rowValue i (by rwa [state.vectorWidth] at inside))
      have scaledWitness := weighted_scale ((residue modulus).comp C) (fun index => residue modulus (columnPower index))
        witness (matrixRow nextWitnesses (degree + 1) pivot) inverse witnessWidth (by
          intro i inside; exact witnessValue i (by rwa [state.witnessWidth] at inside))
      rw [vectorImage, witnessImage, scaledVector, scaledWitness]
      change _ * vectorImage modulus vector = _ * witnessImage modulus witness
      rw [state.paired]
    · rw [unchangedRows row active equal, unchangedWitnesses row active equal]
      exact table.paired row active
  · intro row active
    have newFits : (row + 1) * degree ≤ nextRows.length := by rw [rowsLength]; exact rowFits row active
    rw [← matrix_row_word nextRows degree row row newFits active]
    by_cases equal : row = pivot
    · subst row
      right
      apply word_eq_one
      rw [rowValue pivot pivotActive, mul_comm]
      exact DenseDivision.divisor_inverse_law _ nonzero
    · rw [unchangedRows row active equal, matrix_row_word rows degree row row (rowFits row active) active]
      exact table.diagonal row active

end BulksketchBridge.AffineMultiple
