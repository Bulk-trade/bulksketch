import BulksketchBridge.AffineMultipleNativeWitness
import BulksketchBridge.AffineMultipleNoExhaustion
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

namespace BulksketchBridge.AffineMultiple

open Aeneas.Std Polynomial Algebra.Gf64 DenseReducerAlgebra SliceKernels
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

/-- The exact occupied echelon rows are independent in the quotient.
A least nonzero row multiplier survives at its own diagonal, while
all later rows are zero at that index. -/
theorem occupied_quotient_coefficients_zero (modulus : Slice U64) (degree column : Nat)
    (rows witnesses : Slice U64) (table : WitnessRows modulus degree column rows witnesses)
    (modDegree : (slicePolynomial modulus).natDegree = degree) (coefficient : Nat → Field)
    (vanishes : (∑ i ∈ occupiedRows degree rows,
      residue modulus (C (coefficient i)) * vectorImage modulus (matrixRow rows degree i)) = 0) :
    ∀ i ∈ occupiedRows degree rows, coefficient i = 0 := by
  classical
  intro i occupied
  by_contra nonzero
  let active := occupiedRows degree rows
  let nonzeroRows := active.filter (fun row => coefficient row ≠ 0)
  have found : nonzeroRows.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨occupied, nonzero⟩⟩
  let pivot := nonzeroRows.min' found
  have present : pivot ∈ nonzeroRows := Finset.min'_mem _ _
  obtain ⟨pivotOccupied, pivotNZ⟩ := Finset.mem_filter.mp present
  obtain ⟨pivotRoom, pivotDiagNZ⟩ := Finset.mem_filter.mp pivotOccupied
  have boundedPivot : pivot < degree := Finset.mem_range.mp pivotRoom
  have pivotDiagonal := (table.diagonal pivot boundedPivot).resolve_left pivotDiagNZ
  let combined : Polynomial Field :=
    ∑ row ∈ active, C (coefficient row) * slicePolynomial (matrixRow rows degree row)
  have combinedImage : residue modulus combined = 0 := by
    unfold combined
    rw [map_sum]
    simpa only [map_mul, ← vector_image_polynomial] using vanishes
  have divisible := (AdjoinRoot.mk_eq_zero (f := slicePolynomial modulus)).mp combinedImage
  have fits (row : Nat) (member : row ∈ active) : (row + 1) * degree ≤ rows.length := by
    have activeRow : row < degree := Finset.mem_range.mp (Finset.mem_filter.mp member).1
    exact (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt activeRow)).trans table.rowsRoom
  have low : combined.natDegree ≤ degree - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro index higher
    unfold combined
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro row member
    have width := matrix_row_length rows degree row (fits row member)
    rw [coeff_C_mul, slicePolynomial_coeff, width, ite_eq_right (by omega), mul_zero]
  have combinedZero : combined = 0 := by
    by_contra distinct
    have high := natDegree_le_of_dvd divisible distinct
    rw [modDegree] at high
    omega
  have coefficientAtPivot : combined.coeff pivot = coefficient pivot := by
    unfold combined
    rw [finsetSum_coeff, Finset.sum_eq_single pivot]
    · have room := fits pivot pivotOccupied
      rw [coeff_C_mul, slicePolynomial_coeff, matrix_row_length rows degree pivot room,
        ite_eq_left boundedPivot, matrix_row_word rows degree pivot pivot room boundedPivot,
        pivotDiagonal, show toField (1#u64).bv = 1 from toField_one, mul_one]
    · intro row member different
      rw [coeff_C_mul]
      by_cases earlier : row < pivot
      · have zero : coefficient row = 0 := by
          by_contra rowNZ
          have belongs : row ∈ nonzeroRows := Finset.mem_filter.mpr ⟨member, rowNZ⟩
          exact (Nat.not_le_of_gt earlier) (Finset.min'_le _ _ belongs)
        rw [zero, zero_mul]
      · have later : pivot < row := by omega
        have rowBound : row < degree := Finset.mem_range.mp (Finset.mem_filter.mp member).1
        rw [slicePolynomial_coeff, matrix_row_length rows degree row (fits row member), ite_eq_left boundedPivot,
          table.rowBelow row rowBound pivot later, show toField (0#u64).bv = 0 from toField_zero, mul_zero]
    · intro missing
      exact False.elim (missing pivotOccupied)
  rw [combinedZero, coeff_zero] at coefficientAtPivot
  exact pivotNZ coefficientAtPivot.symm

private theorem quotient_smul (modulus : Slice U64) (factor : Field) (value : Quotient modulus) :
    factor • value = residue modulus (C factor) * value := by
  rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply]

/-- At a column with exactly one stored pivot per prior column, the
paired quotient invariant proves independence of all prior images. -/
theorem prefix_independent_of_occupied_count (modulus : Slice U64) (degree column : Nat)
    (rows witnesses : Slice U64) (table : WitnessRows modulus degree column rows witnesses)
    (modDegree : (slicePolynomial modulus).natDegree = degree) (monic : (slicePolynomial modulus).Monic)
    (count : (occupiedRows degree rows).card = column) :
    PrefixIndependent modulus column := by
  classical
  let active := occupiedRows degree rows
  let cols := Finset.range column
  let rowImages : (↑active : Type) → Quotient modulus := fun i =>
    vectorImage modulus (matrixRow rows degree i.val)
  let columnImages : (↑cols : Type) → Quotient modulus := fun i =>
    residue modulus (columnPower i.val)
  let _ : Module.Finite Field (Quotient modulus) := monic.finite_adjoinRoot
  have rowIndependent : LinearIndependent Field rowImages := by
    apply Fintype.linearIndependent_iff.mpr
    intro a sum i
    let coefficients : Nat → Field := fun index => if member : index ∈ active then a ⟨index, member⟩ else 0
    have sumZero : (∑ index ∈ active,
        residue modulus (C (coefficients index)) * vectorImage modulus (matrixRow rows degree index)) = 0 := by
      rw [← Finset.sum_coe_sort]
      simpa only [rowImages, quotient_smul, coefficients, dite_eq_left (Finset.coe_mem _)] using sum
    have zero := occupied_quotient_coefficients_zero modulus degree column rows witnesses table modDegree coefficients
      sumZero i.val i.property
    simpa only [coefficients, dite_eq_left i.property] using zero
  have spanLe : Submodule.span Field (Set.range rowImages) ≤ Submodule.span Field (Set.range columnImages) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have activeRow : i.val < degree := Finset.mem_range.mp (Finset.mem_filter.mp i.property).1
    have fit : (i.val + 1) * (degree + 1) ≤ witnesses.length :=
      (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt activeRow)).trans table.witnessesRoom
    change vectorImage modulus (matrixRow rows degree i.val) ∈ Submodule.span Field (Set.range columnImages)
    rw [table.paired i.val activeRow, witnessImage, weightedValue, matrix_row_length _ _ _ fit]
    apply Submodule.sum_mem
    intro index member
    have inside := Finset.mem_range.mp member
    by_cases earlier : index < column
    · let j : (↑cols : Type) := ⟨index, Finset.mem_range.mpr earlier⟩
      have basis : columnImages j ∈ Submodule.span Field (Set.range columnImages) :=
        Submodule.subset_span ⟨j, rfl⟩
      have scaled := Submodule.smul_mem (Submodule.span Field (Set.range columnImages))
        (toField (matrixRow witnesses (degree + 1) i.val)[index]!.bv) basis
      simpa only [columnImages, j, quotient_smul, RingHom.comp_apply] using scaled
    · rw [table.witnessAfter i.val activeRow index inside (Nat.le_of_not_gt earlier)]
      change ((residue modulus).comp C) (toField 0) * _ ∈ _
      rw [toField_zero, map_zero, zero_mul]
      exact Submodule.zero_mem _
  have dim := Submodule.finrank_mono spanLe
  have rowDim := finrank_span_eq_card rowIndependent
  have columnIndependent : LinearIndependent Field columnImages := by
    apply linearIndependent_iff_card_le_finrank_span.mpr
    have rowCount : Fintype.card (↑active : Type) = column := by rw [Fintype.card_coe]; exact count
    rw [rowCount] at rowDim
    change Fintype.card (↑cols : Type) ≤ Module.finrank Field (Submodule.span Field (Set.range columnImages))
    rw [Fintype.card_coe, Finset.card_range, ← rowDim]
    exact dim
  intro coefficients vanishes i room
  let a : (↑cols : Type) → Field := fun j => coefficients j.val
  have zero : (∑ j, a j • columnImages j) = 0 := by
    have compared := Finset.sum_coe_sort cols (fun index =>
      residue modulus (C (coefficients index)) * residue modulus (columnPower index))
    simpa only [a, columnImages, quotient_smul] using compared.trans vanishes
  exact (Fintype.linearIndependent_iff.mp columnIndependent a zero) ⟨i, Finset.mem_range.mpr room⟩

end BulksketchBridge.AffineMultiple
