import BulksketchBridge.AffineMultipleWitnessWords
import BulksketchBridge.AffineMultipleColumn

namespace BulksketchBridge.AffineMultiple

open Aeneas.Std Polynomial Algebra.Gf64 DenseReducerAlgebra SliceKernels
open DenseCoefficient RebuiltLfsr BmEntry
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

abbrev Quotient (modulus : Slice U64) := AdjoinRoot (slicePolynomial modulus)

def columnExponent : Nat → Nat
  | 0 => 0
  | index + 1 => 2 ^ index

noncomputable def columnPower (index : Nat) : Polynomial Field := X ^ columnExponent index

noncomputable def weightedValue {R : Type} [CommSemiring R]
    (cast : Field →+* R) (weights : Nat → R) (words : Slice U64) : R :=
  ∑ index ∈ Finset.range words.length, cast (toField words[index]!.bv) * weights index

private theorem weighted_axpy {R : Type} [CommSemiring R] (cast : Field →+* R) (weights : Nat → R)
    (destination row written : Slice U64) (factor : U64)
    (rowWidth : row.length = destination.length) (outputWidth : written.length = destination.length)
    (words : ∀ i < destination.length,
      toField written[i]!.bv = toField destination[i]!.bv + toField factor.bv * toField row[i]!.bv) :
    weightedValue cast weights written =
      weightedValue cast weights destination + cast (toField factor.bv) * weightedValue cast weights row := by
  unfold weightedValue
  rw [outputWidth, rowWidth, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i member
  rw [words i (Finset.mem_range.mp member), map_add, map_mul, add_mul, mul_assoc]

noncomputable def packedWitness (words : Slice U64) : Polynomial Field :=
  weightedValue C columnPower words

noncomputable def vectorImage (modulus vector : Slice U64) : Quotient modulus :=
  weightedValue ((residue modulus).comp C) (fun index => residueX modulus ^ index) vector

noncomputable def witnessImage (modulus witness : Slice U64) : Quotient modulus :=
  weightedValue ((residue modulus).comp C) (fun index => residue modulus (columnPower index)) witness

theorem vector_image_polynomial (modulus words : Slice U64) :
    vectorImage modulus words = residue modulus (slicePolynomial words) := by
  unfold vectorImage weightedValue
  rw [show slicePolynomial words = ∑ i ∈ Finset.range words.length,
    monomial i (toField words[i]!.bv) from rfl, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RingHom.comp_apply, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul, C_mul_X_pow_eq_monomial]

theorem witness_image_polynomial (modulus words : Slice U64) :
    witnessImage modulus words = residue modulus (packedWitness words) := by
  unfold witnessImage packedWitness weightedValue
  rw [map_sum]
  simp only [map_mul, RingHom.comp_apply]

private theorem image_of_zero (modulus vector : Slice U64)
    (zero : ∀ i < vector.length, vector[i]! = 0#u64) :
    vectorImage modulus vector = 0 := by
  unfold vectorImage weightedValue
  apply Finset.sum_eq_zero
  intro i member
  rw [zero i (Finset.mem_range.mp member)]
  change ((residue modulus).comp C) (toField 0) * _ = 0
  rw [toField_zero, map_zero, zero_mul]

theorem word_eq_zero (word : U64) (zero : toField word.bv = 0) : word = 0#u64 := by
  apply U64.bv_eq_imp_eq
  exact toField_injective (zero.trans toField_zero.symm)

theorem word_eq_one (word : U64) (one : toField word.bv = 1) : word = 1#u64 := by
  apply U64.bv_eq_imp_eq
  exact toField_injective (one.trans toField_one.symm)

/-- The stored elimination rows carry their affine preimage witnesses.
Rows have no coefficients below their index and prior witnesses have no
coefficients at or beyond the current column. Occupied diagonals are one. -/
structure WitnessRows (modulus : Slice U64) (degree column : Nat)
    (rows witnesses : Slice U64) : Prop where
  columnRoom : column ≤ degree
  rowsRoom : degree * degree ≤ rows.length
  witnessesRoom : degree * (degree + 1) ≤ witnesses.length
  rowBelow : ∀ row < degree, ∀ i < row, (matrixRow rows degree row)[i]! = 0#u64
  witnessAfter : ∀ row < degree, ∀ i < degree + 1, column ≤ i →
    (matrixRow witnesses (degree + 1) row)[i]! = 0#u64
  paired : ∀ row < degree, vectorImage modulus (matrixRow rows degree row) =
    witnessImage modulus (matrixRow witnesses (degree + 1) row)
  diagonal : ∀ row < degree, rows[row * degree + row]! = 0#u64 ∨ rows[row * degree + row]! = 1#u64

structure ColumnWitness (modulus : Slice U64) (degree column : Nat) (vector witness : Slice U64) : Prop where
  vectorWidth : vector.length = degree
  witnessWidth : witness.length = degree + 1
  paired : vectorImage modulus vector = witnessImage modulus witness
  leading : witness[column]! = 1#u64
  future : ∀ i < degree + 1, column < i → witness[i]! = 0#u64

/-- One original paired axpy preserves the quotient witness and the
current leading coefficient, and zeros the processed coefficient. -/
theorem eliminate_row_witness (modulus : Slice U64) (degree column row : Nat)
    (rows witnesses vector witness : Slice U64)
    (table : WitnessRows modulus degree column rows witnesses)
    (state : ColumnWitness modulus degree column vector witness)
    (active : row < degree) (occupied : rows[row * degree + row]! ≠ 0#u64)
    (previous : ∀ i < row, vector[i]! = 0#u64) :
    let updated := eliminateRow degree column rows witnesses row vector witness
    ColumnWitness modulus degree column updated.1 updated.2 ∧
      ∀ i < row + 1, updated.1[i]! = 0#u64 := by
  dsimp only
  obtain ⟨vectorWords, witnessWords⟩ := eliminate_row_words degree column rows witnesses row vector witness
    active table.columnRoom table.rowsRoom table.witnessesRoom state.vectorWidth state.witnessWidth
    (table.rowBelow row active) (fun i inside after => table.witnessAfter row active i inside (by omega))
  obtain ⟨vectorLength, witnessLength⟩ := eliminate_row_lengths degree column rows witnesses row vector witness
  have rowFits : (row + 1) * degree ≤ rows.length :=
    (Nat.mul_le_mul_right degree (Nat.succ_le_of_lt active)).trans table.rowsRoom
  have witnessFits : (row + 1) * (degree + 1) ≤ witnesses.length :=
    (Nat.mul_le_mul_right (degree + 1) (Nat.succ_le_of_lt active)).trans table.witnessesRoom
  have rowWidth := (matrix_row_length rows degree row rowFits).trans state.vectorWidth.symm
  have priorWidth := (matrix_row_length witnesses (degree + 1) row witnessFits).trans state.witnessWidth.symm
  have mappedVector := weighted_axpy ((residue modulus).comp C) (fun index => residueX modulus ^ index)
    vector (matrixRow rows degree row) (eliminateRow degree column rows witnesses row vector witness).1
    vector[row]! rowWidth vectorLength vectorWords
  have mappedWitness := weighted_axpy ((residue modulus).comp C) (fun index => residue modulus (columnPower index))
    witness (matrixRow witnesses (degree + 1) row) (eliminateRow degree column rows witnesses row vector witness).2
    vector[row]! priorWidth witnessLength witnessWords
  refine ⟨⟨vectorLength.trans state.vectorWidth, witnessLength.trans state.witnessWidth, ?_, ?_, ?_⟩, ?_⟩
  ·
    rw [vectorImage, mappedVector, witnessImage, mappedWitness]
    change vectorImage modulus vector + _ * vectorImage modulus (matrixRow rows degree row) =
      witnessImage modulus witness + _ * witnessImage modulus (matrixRow witnesses (degree + 1) row)
    rw [state.paired, table.paired row active]
  · apply word_eq_one
    have inside : column < witness.length := by
      rw [state.witnessWidth]
      exact Nat.lt_succ_of_le table.columnRoom
    rw [witnessWords column inside, state.leading, table.witnessAfter row active column
      (by have := table.columnRoom; omega) (Nat.le_refl _)]
    simp only [show toField (1#u64).bv = 1 from toField_one,
      show toField (0#u64).bv = 0 from toField_zero, mul_zero, add_zero]
  · intro i inside later
    apply word_eq_zero
    rw [witnessWords i (by rwa [state.witnessWidth]), state.future i inside later,
      table.witnessAfter row active i inside (by omega)]
    simp only [show toField (0#u64).bv = 0 from toField_zero, mul_zero, add_zero]
  · intro i processed
    apply word_eq_zero
    have inside : i < vector.length := by rw [state.vectorWidth]; omega
    rw [vectorWords i inside]
    by_cases below : i < row
    · rw [previous i below, table.rowBelow row active i below]
      simp only [show toField (0#u64).bv = 0 from toField_zero, mul_zero, add_zero]
    · have equal : i = row := by omega
      subst i
      rw [matrix_row_word rows degree row row rowFits active, (table.diagonal row active).resolve_left occupied,
        show toField (1#u64).bv = 1 from toField_one, mul_one, CharTwo.add_self_eq_zero]

/-- The deterministic native pivot-search model preserves the quotient
relation. Exhausting its row cursor yields the zero coefficient vector. -/
theorem pivot_search_witness (modulus : Slice U64) (degree column : Nat)
    (rows witnesses : Slice U64) (table : WitnessRows modulus degree column rows witnesses)
    (fuel row : Nat) (vector witness : Slice U64) (remaining : row + fuel = degree)
    (state : ColumnWitness modulus degree column vector witness)
    (previous : ∀ i < row, vector[i]! = 0#u64) :
    let output := pivotSearch degree column rows witnesses fuel row vector witness
    ColumnWitness modulus degree column output.1 output.2.1 ∧
      (output.2.2 = none → ∀ i < degree, output.1[i]! = 0#u64) := by
  induction fuel generalizing row vector witness with
  | zero =>
    simp only [pivotSearch, true_implies]
    exact ⟨state, by simpa only [show row = degree by omega] using previous⟩
  | succ fuel ih =>
    have active : row < degree := by omega
    by_cases skip : vector[row]! = 0#u64
    · simp only [pivotSearch, pivotRow, skip, ite_true]
      exact ih (row + 1) vector witness (by omega) state (by
        intro i bound
        by_cases lower : i < row
        · exact previous i lower
        · simpa only [show i = row by omega] using skip)
    · by_cases vacant : rows[row * degree + row]! = 0#u64
      · simp only [pivotSearch, pivotRow, ite_eq_right skip, vacant, ite_true]
        exact ⟨state, by intro impossible; contradiction⟩
      · have preserved := eliminate_row_witness modulus degree column row rows witnesses vector witness
          table state active vacant previous
        simp only [pivotSearch, pivotRow, ite_eq_right skip, ite_eq_right vacant]
        exact ih (row + 1) _ _ (by omega) preserved.1 preserved.2

/-- A dependent column of the actual pivot recurrence yields a monic-leading
coefficient witness whose polynomial is divisible by the fixed modulus. -/
theorem dependent_pivot_witness (modulus : Slice U64) (degree column : Nat)
    (rows witnesses vector witness : Slice U64)
    (table : WitnessRows modulus degree column rows witnesses)
    (state : ColumnWitness modulus degree column vector witness)
    (dependent : (pivotSearch degree column rows witnesses degree 0 vector witness).2.2 = none) :
    let answer := (pivotSearch degree column rows witnesses degree 0 vector witness).2.1
    slicePolynomial modulus ∣ packedWitness answer ∧ answer[column]! = 1#u64 ∧
      ∀ i < degree + 1, column < i → answer[i]! = 0#u64 := by
  dsimp only
  obtain ⟨output, zeros⟩ := pivot_search_witness modulus degree column rows witnesses table degree 0 vector witness
    (by simp) state (by intro i impossible; omega)
  refine ⟨(AdjoinRoot.mk_eq_zero (f := slicePolynomial modulus)).mp ?_, output.leading, output.future⟩
  rw [← witness_image_polynomial, ← output.paired]
  exact image_of_zero modulus _ (by simpa only [output.vectorWidth] using zeros dependent)

/-- A selected pivot is the first nonzero coefficient of the reduced
vector, because the exact earlier row steps zero every preceding slot. -/
theorem selected_pivot_below_zero (modulus : Slice U64) (degree column : Nat)
    (rows witnesses : Slice U64) (table : WitnessRows modulus degree column rows witnesses)
    (fuel row : Nat) (vector witness : Slice U64) (remaining : row + fuel = degree)
    (state : ColumnWitness modulus degree column vector witness)
    (previous : ∀ i < row, vector[i]! = 0#u64) (pivot : Nat)
    (selected : (pivotSearch degree column rows witnesses fuel row vector witness).2.2 = some pivot) :
    ∀ i < pivot, (pivotSearch degree column rows witnesses fuel row vector witness).1[i]! = 0#u64 := by
  induction fuel generalizing row vector witness with
  | zero => contradiction
  | succ fuel ih =>
    have active : row < degree := by omega
    by_cases skip : vector[row]! = 0#u64
    · simp only [pivotSearch, pivotRow, skip, ite_true] at selected ⊢
      exact ih (row + 1) vector witness (by omega) state (by
        intro i bound
        by_cases lower : i < row
        · exact previous i lower
        · simpa only [show i = row by omega] using skip) selected
    · by_cases vacant : rows[row * degree + row]! = 0#u64
      · simp only [pivotSearch, pivotRow, ite_eq_right skip, vacant, ite_true, Option.some.injEq] at selected ⊢
        subst pivot
        exact previous
      · have preserved := eliminate_row_witness modulus degree column row rows witnesses vector witness
          table state active vacant previous
        simp only [pivotSearch, pivotRow, ite_eq_right skip, ite_eq_right vacant] at selected ⊢
        exact ih (row + 1) _ _ (by omega) preserved.1 preserved.2 selected

end BulksketchBridge.AffineMultiple
