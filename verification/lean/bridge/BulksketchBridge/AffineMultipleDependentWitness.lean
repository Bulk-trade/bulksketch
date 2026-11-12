import BulksketchBridge.AffineMultipleWitness
import BulksketchBridge.AffineMultipleLoop
import BulksketchBridge.DenseGcd

namespace BulksketchBridge.AffineMultiple

open Aeneas.Std Polynomial Algebra.Gf64 DenseReducerAlgebra SliceKernels
open DenseCoefficient RebuiltLfsr
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

theorem column_exponent_strict : StrictMono columnExponent := by
  apply strictMono_nat_of_lt_succ
  intro i
  cases i with
  | zero => decide
  | succ i =>
    change (2 : Nat) ^ i < 2 ^ (i + 1)
    exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self i)

theorem packed_coeff_at (words : Slice U64) (index : Nat) :
    (packedWitness words).coeff (columnExponent index) =
      if index < words.length then toField words[index]!.bv else 0 := by
  simp only [packedWitness, weightedValue, columnPower, C_mul_X_pow_eq_monomial, finsetSum_coeff]
  rw [Finset.sum_eq_single index]
  · by_cases inside : index < words.length
    · simp [inside]
    · rw [ite_eq_right inside, coeff_monomial, ite_eq_left rfl]
      have absent : words.val.length ≤ index := by change words.length ≤ index; omega
      rw [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, List.getElem?_eq_none absent]
      exact toField_zero
  · intro other _ different
    rw [coeff_monomial, ite_eq_right (fun eq => different (column_exponent_strict.injective eq))]
  · intro absent
    rw [coeff_monomial, ite_eq_left rfl]
    have outside : words.val.length ≤ index := by
      change words.length ≤ index
      exact Nat.le_of_not_gt (fun h => absent (Finset.mem_range.mpr h))
    rw [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, List.getElem?_eq_none outside]
    exact toField_zero

theorem packed_monic_degree (words : Slice U64) (column : Nat)
    (width : words.length = column + 1) (one : words[column]! = 1#u64) :
    (packedWitness words).Monic ∧ (packedWitness words).natDegree = columnExponent column := by
  have coeff : (packedWitness words).coeff (columnExponent column) = 1 := by
    rw [packed_coeff_at, ite_eq_left (by omega), one]
    exact toField_one
  have upper : (packedWitness words).natDegree ≤ columnExponent column := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro exponent higher
    simp only [packedWitness, weightedValue, columnPower, C_mul_X_pow_eq_monomial, finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro index member
    have atMost : index ≤ column := by have := Finset.mem_range.mp member; omega
    have smaller : columnExponent index < exponent :=
      (column_exponent_strict.monotone atMost).trans_lt higher
    rw [coeff_monomial, ite_eq_right (Nat.ne_of_lt smaller)]
  have lower : columnExponent column ≤ (packedWitness words).natDegree :=
    le_natDegree_of_ne_zero (by rw [coeff]; exact one_ne_zero)
  have degree := le_antisymm upper lower
  refine ⟨?_, degree⟩
  change (packedWitness words).leadingCoeff = 1
  rwa [← coeff_natDegree, degree]

theorem packed_prefix_zero (words : Slice U64) (count : Nat) (room : count ≤ words.length)
    (zeros : ∀ i < words.length, count ≤ i → words[i]! = 0#u64) :
    packedWitness (prefixSlice words count) = packedWitness words := by
  unfold packedWitness weightedValue
  rw [prefix_length, Nat.min_eq_left room]
  calc
    _ = ∑ i ∈ Finset.range count, C (toField words[i]!.bv) * columnPower i := by
      apply Finset.sum_congr rfl
      intro i active
      rw [prefix_word _ _ _ (Finset.mem_range.mp active)]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono room)
      intro i active beyond
      have large : count ≤ i := Nat.le_of_not_gt (fun smaller => beyond (Finset.mem_range.mpr smaller))
      rw [zeros i (Finset.mem_range.mp active) large]
      change C (toField 0) * columnPower i = 0
      rw [toField_zero, map_zero, zero_mul]

theorem zero_words_word (shape : Slice U64) (index : Nat) (inside : index < shape.length) :
    (zeroWords shape)[index]! = 0#u64 := by
  simp only [zeroWords, Slice.from_val, Slice.getElem!_Nat_eq, List.getElem!_replicate, inside]

theorem initial_witness_word (column : Usize) (shape : Slice U64) (index : Nat)
    (inside : index < shape.length) (columnRoom : column.val < shape.length) :
    (initialWitness column shape)[index]! = if index = column.val then 1#u64 else 0#u64 := by
  unfold initialWitness
  by_cases same : index = column.val
  · subst index
    rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq]
    · simp only [ite_true]
    · simpa only [zero_length] using columnRoom
  · rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm same), ← Slice.getElem!_Nat_eq,
      zero_words_word _ _ inside, ite_eq_right same]

theorem initial_witness_image (modulus : Slice U64) (column : Usize) (shape : Slice U64)
    (room : column.val < shape.length) :
    witnessImage modulus (initialWitness column shape) = residue modulus (columnPower column.val) := by
  unfold witnessImage weightedValue
  simp only [initialWitness, Slice.setAtNat_length, zero_length]
  change (∑ i ∈ Finset.range shape.length,
    ((residue modulus).comp C) (toField ((zeroWords shape).setAtNat column.val 1#u64)[i]!.bv) *
      residue modulus (columnPower i)) = _
  rw [Finset.sum_eq_single column.val]
  · change ((residue modulus).comp C) (toField (initialWitness column shape)[column.val]!.bv) * _ = _
    rw [initial_witness_word column shape column.val room room, ite_eq_left rfl]
    change ((residue modulus).comp C) (toField 1) * _ = _
    rw [toField_one, map_one, one_mul]
  · intro i active different
    change ((residue modulus).comp C) (toField (initialWitness column shape)[i]!.bv) * _ = 0
    rw [initial_witness_word column shape i (Finset.mem_range.mp active) room, ite_eq_right different]
    change ((residue modulus).comp C) (toField 0) * _ = 0
    rw [toField_zero, map_zero, zero_mul]
  · intro absent
    exact (absent (Finset.mem_range.mpr room)).elim

/-- The original dependent column returns a monic packed affine polynomial
divisible by the modulus, assuming the preceding row table and residue
have their quotient meanings. -/
theorem native_dependent_column_witness {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (scaleLaw : TimesXMod.ExactScaleXor kernels) (restores : ColumnRestores)
    (shape : ColumnShape) (iter next : ColumnIter) (state : ColumnState)
    (column : Usize) (ready : columnReady shape column state)
    (yielded : nextColumn iter = .ok (some column, next))
    (rows : WitnessRows shape.polynomial shape.degree.val column.val state.rows state.witnesses)
    (residueMeaning : vectorImage shape.polynomial state.residue = residue shape.polynomial (columnPower column.val))
    (dependent : (searchedColumn shape state column).2.2 = none) :
    ∃ length affine factors work,
      columnBody square kernels restores shape iter state = .ok (.done (length, factors, affine, work, state.raw)) ∧
      length.val = column.val + 1 ∧
      let polynomial := packedWitness (prefixSlice affine length.val)
      polynomial.Monic ∧ polynomial.natDegree = columnExponent column.val ∧
      slicePolynomial shape.polynomial ∣ polynomial := by
  obtain ⟨layout, residueWidth, affineRoom⟩ := ready
  have witnessWidth : state.witness.length = shape.degree.val + 1 :=
    layout.witnessWidth.trans layout.widthValue
  have witnessRoom : column.val < state.witness.length := by rw [witnessWidth]; exact Nat.lt_succ_of_le rows.columnRoom
  have input : ColumnWitness shape.polynomial shape.degree.val column.val state.residue
      (initialWitness column state.witness) := by
    refine ⟨residueWidth, by simp only [initialWitness, Slice.setAtNat_length, zero_length, witnessWidth], ?_, ?_, ?_⟩
    · rw [residueMeaning, initial_witness_image _ _ _ witnessRoom]
    · rw [initial_witness_word _ _ _ witnessRoom witnessRoom, ite_eq_left rfl]
    · intro i inside later
      rw [initial_witness_word _ _ _ (by rwa [witnessWidth]) witnessRoom, ite_eq_right (by omega)]
  have semantic := dependent_pivot_witness shape.polynomial shape.degree.val column.val
    state.rows state.witnesses state.residue (initialWitness column state.witness) rows input dependent
  obtain ⟨certified, _⟩ := pivot_search_witness shape.polynomial shape.degree.val column.val
    state.rows state.witnesses rows shape.degree.val 0 state.residue (initialWitness column state.witness)
      (by simp) input (by intro i impossible; omega)
  obtain ⟨length, lengthValue, native⟩ :=
    dependent_column_refines square kernels scaleLaw restores shape iter next state column ⟨layout, residueWidth, affineRoom⟩ yielded dependent
  let result := searchedColumn shape state column
  let truncated := prefixSlice result.2.1 (column.val + 1)
  have resultWidth : result.2.1.length = shape.degree.val + 1 := certified.witnessWidth
  have truncWidth : truncated.length = column.val + 1 := by
    rw [show truncated.length = min (column.val + 1) result.2.1.length from prefix_length _ _,
      Nat.min_eq_left (by rw [resultWidth]; exact Nat.succ_le_succ rows.columnRoom)]
  have written : prefixSlice (restorePrefix shape.affine truncated) length.val = truncated := by
    rw [lengthValue, ← truncWidth]
    exact DenseGcd.prefix_restored _ _ (truncWidth.symm ▸ Nat.succ_le_of_lt affineRoom)
  have headOne : truncated[column.val]! = 1#u64 := by
    change (prefixSlice result.2.1 (column.val + 1))[column.val]! = _
    rw [prefix_word _ _ _ (Nat.lt_succ_self _)]
    exact certified.leading
  have ⟨monic, degree⟩ := packed_monic_degree truncated column.val truncWidth headOne
  have whole : packedWitness truncated = packedWitness result.2.1 := packed_prefix_zero _ _
    (by rw [resultWidth]; exact Nat.succ_le_succ rows.columnRoom)
    (by intro i inside beyond; exact certified.future i (by rwa [resultWidth] at inside) (by omega))
  refine ⟨length, restorePrefix shape.affine truncated,
    restores.factors (state.rows, restores.witnesses state.witnesses),
    restores.work (state.residue, restores.vector (result.1, restores.witness result.2.1)), native, lengthValue, ?_⟩
  rw [written]
  exact ⟨monic, degree, whole.symm ▸ semantic.1⟩

end BulksketchBridge.AffineMultiple
