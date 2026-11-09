import BulksketchBridge.AffineMultipleDependentWitness

namespace BulksketchBridge.AffineMultiple

open Aeneas.Std Polynomial Algebra.Gf64 DenseReducerAlgebra SliceKernels DenseCoefficient RebuiltLfsr
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

/-- The original prefix columns admit no nonzero coefficient relation in
the quotient. This is the algebraic independence premise for minimality. -/
def PrefixIndependent (modulus : Slice U64) (column : Nat) : Prop :=
  ∀ coefficients : Nat → Field,
    (∑ i ∈ Finset.range column,
      residue modulus (C (coefficients i)) * residue modulus (columnPower i)) = 0 →
    ∀ i < column, coefficients i = 0

private theorem field_word_zero (word : U64) (zero : toField word.bv = 0) : word = 0#u64 := by
  apply U64.bv_eq_imp_eq
  exact toField_injective (zero.trans toField_zero.symm)

/-- No nonzero represented affine multiple can have degree smaller than
the next column when the earlier residue columns are independent. -/
theorem packed_degree_lower_bound (modulus words : Slice U64) (column : Nat)
    (independent : PrefixIndependent modulus column)
    (nonzero : packedWitness words ≠ 0)
    (multiple : slicePolynomial modulus ∣ packedWitness words) :
    columnExponent column ≤ (packedWitness words).natDegree := by
  by_contra smaller
  have less : (packedWitness words).natDegree < columnExponent column := Nat.lt_of_not_ge smaller
  have tailZero : ∀ i < words.length, column ≤ i → words[i]! = 0#u64 := by
    intro i inside later
    have vanish : (packedWitness words).coeff (columnExponent i) = 0 :=
      coeff_eq_zero_of_natDegree_lt (less.trans_le (column_exponent_strict.monotone later))
    rw [packed_coeff_at, ite_eq_left inside] at vanish
    exact field_word_zero _ vanish
  let count := min column words.length
  have countRoom : count ≤ words.length := Nat.min_le_right _ _
  have countColumn : count ≤ column := Nat.min_le_left _ _
  have truncated := packed_prefix_zero words count countRoom (by
    intro i inside beyond
    have later : column ≤ i := by
      by_cases order : column ≤ words.length
      · simpa only [count, Nat.min_eq_left order] using beyond
      · have opposite : words.length ≤ column := by omega
        have tooLarge : words.length ≤ i := by
          simpa only [count, Nat.min_eq_right opposite] using beyond
        omega
    exact tailZero i inside later)
  let coefficients : Nat → Field := fun i => if i < words.length then toField words[i]!.bv else 0
  have rootZero : residue modulus (packedWitness words) = 0 :=
    (AdjoinRoot.mk_eq_zero (f := slicePolynomial modulus)).mpr multiple
  have prefixImage : witnessImage modulus (prefixSlice words count) = 0 := by
    rw [witness_image_polynomial, truncated, rootZero]
  have prefixSum : (∑ i ∈ Finset.range count,
      residue modulus (C (coefficients i)) * residue modulus (columnPower i)) = 0 := by
    rw [witnessImage, weightedValue, prefix_length, Nat.min_eq_left countRoom] at prefixImage
    calc
      _ = ∑ i ∈ Finset.range count,
          ((residue modulus).comp C) (toField (prefixSlice words count)[i]!.bv) *
            residue modulus (columnPower i) := by
        apply Finset.sum_congr rfl
        intro i member
        have within := Finset.mem_range.mp member
        rw [prefix_word _ _ _ within, RingHom.comp_apply]
        simp only [coefficients, ite_eq_left (within.trans_le countRoom)]
      _ = 0 := prefixImage
  have fullSum : (∑ i ∈ Finset.range column,
      residue modulus (C (coefficients i)) * residue modulus (columnPower i)) = 0 := by
    rw [← prefixSum]
    symm
    apply Finset.sum_subset (Finset.range_mono countColumn)
    intro i member missing
    have within := Finset.mem_range.mp member
    have outside : ¬ i < words.length := by
      intro inside
      exact missing (Finset.mem_range.mpr (Nat.lt_min.mpr ⟨within, inside⟩))
    simp only [coefficients, ite_eq_right outside, map_zero, zero_mul]
  have allCoefficientsZero := independent coefficients fullSum
  apply nonzero
  unfold packedWitness weightedValue
  apply Finset.sum_eq_zero
  intro i member
  have inside := Finset.mem_range.mp member
  by_cases earlier : i < column
  · have zero := allCoefficientsZero i earlier
    simp only [coefficients, ite_eq_left inside] at zero
    rw [zero, map_zero, zero_mul]
  · rw [tailZero i inside (Nat.le_of_not_gt earlier)]
    change C (toField 0) * columnPower i = 0
    rw [toField_zero, map_zero, zero_mul]

/-- Conditional minimality for the actual dependent column's emitted
prefix, under quotient correctness and independence of the preceding
columns. -/
theorem native_dependent_column_least {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (scaleLaw : TimesXMod.ExactScaleXor kernels) (restores : ColumnRestores)
    (shape : ColumnShape) (iter next : ColumnIter) (state : ColumnState)
    (column : Usize) (ready : columnReady shape column state)
    (yielded : nextColumn iter = .ok (some column, next))
    (rows : WitnessRows shape.polynomial shape.degree.val column.val state.rows state.witnesses)
    (residueMeaning : vectorImage shape.polynomial state.residue = residue shape.polynomial (columnPower column.val))
    (independent : PrefixIndependent shape.polynomial column.val)
    (dependent : (searchedColumn shape state column).2.2 = none) :
    ∃ length affine factors work,
      columnBody square kernels restores shape iter state = .ok (.done (length, factors, affine, work, state.raw)) ∧
      length.val = column.val + 1 ∧
      let polynomial := packedWitness (prefixSlice affine length.val)
      polynomial.Monic ∧ slicePolynomial shape.polynomial ∣ polynomial ∧
        ∀ other : Slice U64, packedWitness other ≠ 0 →
          slicePolynomial shape.polynomial ∣ packedWitness other →
          polynomial.natDegree ≤ (packedWitness other).natDegree := by
  obtain ⟨length, affine, factors, work, normal, lenValue, monic, degree, multiple⟩ :=
    native_dependent_column_witness square kernels scaleLaw restores shape iter next state column
      ready yielded rows residueMeaning dependent
  refine ⟨length, affine, factors, work, normal, lenValue, monic, multiple, ?_⟩
  intro other nonzero divides
  rw [degree]
  exact packed_degree_lower_bound shape.polynomial other column.val independent nonzero divides

end BulksketchBridge.AffineMultiple
