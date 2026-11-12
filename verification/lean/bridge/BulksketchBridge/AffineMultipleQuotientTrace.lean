import BulksketchBridge.AffineMultipleStoredWitness
import BulksketchBridge.AffineMultipleWrapper
import BulksketchBridge.AffineSplitterEvaluation

namespace BulksketchBridge.AffineMultiple

open Aeneas Aeneas.Std Result Polynomial Algebra.Gf64 DenseReducerAlgebra SliceKernels
open DenseCoefficient RebuiltLfsr BmEntry
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

private theorem initialized_monomial (shape : Slice U64) (index : Nat) (word : U64)
    (inside : index < shape.length) :
    slicePolynomial ((zeroWords shape).setAtNat index word) = monomial index (toField word.bv) := by
  ext i
  rw [slicePolynomial_coeff, Slice.setAtNat_length, zero_length, coeff_monomial]
  by_cases same : index = i
  · subst i
    rw [ite_eq_left inside, ite_eq_left rfl, Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq]
    rwa [zero_length]
  · rw [ite_eq_right same]
    by_cases active : i < shape.length
    · rw [ite_eq_left active, Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ same]
      simp only [zeroWords, Slice.from_val, List.getElem!_replicate, active]
      exact toField_zero
    · rw [ite_eq_right active]

private theorem prefix_full (words : Slice U64) (degree : Nat) (width : words.length = degree) :
    prefixSlice words degree = words := by
  apply Slice.ext
  simp only [prefixSlice, Slice.from_val]
  exact List.take_of_length_le width.le

private theorem mod_by_monic_image (modulus : Slice U64) (p : Polynomial Field) :
    residue modulus (p %ₘ slicePolynomial modulus) = residue modulus p := by
  have decomposition := congrArg (residue modulus) (modByMonic_add_div p (slicePolynomial modulus))
  simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, zero_mul, add_zero] using decomposition

private theorem column_power_step (column : Nat) (positive : 0 < column) :
    columnPower (column + 1) = columnPower column ^ 2 := by
  cases column with
  | zero => contradiction
  | succ n =>
    change (X : Polynomial Field) ^ (2 ^ (n + 1)) = (X ^ (2 ^ n)) ^ 2
    rw [Nat.pow_succ, pow_mul]

/-- The exact original residue continuation advances the column image
from 1 to X, and then squares it in the same quotient. -/
theorem continued_residue_image {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (shape : ColumnShape) (state : ColumnState) (column : Usize)
    (vector nextResidue nextVector : Slice U64) (nextRaw : Slice bulksketch.types.RawProduct)
    (active : column.val < shape.degree.val) (minimum : 2 ≤ shape.degree.val)
    (residueWidth : state.residue.length = shape.degree.val) (vectorWidth : vector.length = shape.degree.val)
    (rawRoom : 2 * shape.degree.val < state.raw.length)
    (fullSquare : AffineSplitter.FullSquareLaw square kernels shape.polynomial shape.table shape.degree.val)
    (current : vectorImage shape.polynomial state.residue = residue shape.polynomial (columnPower column.val))
    (advance : advancedResidue square kernels shape state column vector = .ok (nextResidue, nextVector, nextRaw)) :
    vectorImage shape.polynomial nextResidue = residue shape.polynomial (columnPower (column.val + 1)) ∧
      nextRaw.length = state.raw.length := by
  by_cases first : column = 0#usize
  · rw [advancedResidue, ite_eq_left first] at advance
    have eq := Result.ok_injective advance
    have reset : (zeroWords state.residue).setAtNat 1 1#u64 = nextResidue := congrArg Prod.fst eq
    have rawSame : state.raw = nextRaw := congrArg (fun pair => pair.2.2) eq
    refine ⟨?_, congrArg Slice.length rawSame.symm⟩
    rw [← reset, vector_image_polynomial, initialized_monomial _ _ _ (by rw [residueWidth]; omega), first]
    change residue shape.polynomial (monomial 1 (toField 1)) = residue shape.polynomial (X ^ 1)
    rw [toField_one, ← C_mul_X_pow_eq_monomial, map_one, one_mul]
  · have last : column ≠ shape.degree := by
      intro equal
      rw [equal] at active
      omega
    obtain ⟨size, squared, scratch, squareNormal, squareWidth, scratchWidth, represented⟩ :=
      fullSquare state.residue vector state.raw residueWidth.le vectorWidth.ge rawRoom
    have called : square RootSetup.gf64Dictionary kernels state.residue shape.polynomial shape.table vector state.raw =
      .ok (size, squared, scratch) := squareNormal
    rw [advancedResidue, ite_eq_right first, ite_eq_right last, called, bind_ok] at advance
    have eq := Result.ok_injective advance
    have residueEq : squared = nextResidue := congrArg Prod.fst eq
    have scratchEq : scratch = nextRaw := congrArg (fun output => output.2.2) eq
    refine ⟨?_, scratchEq.symm ▸ scratchWidth⟩
    have width : squared.length = shape.degree.val := squareWidth.trans vectorWidth
    have actual : slicePolynomial squared = (slicePolynomial state.residue ^ 2) %ₘ slicePolynomial shape.polynomial := by
      rwa [prefix_full _ _ width] at represented
    have positive : 0 < column.val := by
      by_contra inactive
      exact first (UScalar.eq_of_val_eq (by change column.val = 0; omega))
    rw [← residueEq, vector_image_polynomial, actual, mod_by_monic_image, map_pow,
      ← vector_image_polynomial, current, column_power_step column.val positive, map_pow]

/-- Initially both matrices are zero and the residue represents the
constant column. This establishes the quotient invariant for column zero. -/
theorem prepared_witness_rows (degree : Usize) (polynomial table factors affine work : Slice U64)
    (raw : Slice bulksketch.types.RawProduct)
    (arena : ColumnArena (preparedShape degree polynomial table affine)
      (preparedState degree.val factors work raw))
    (positive : 0 < degree.val) :
    let state := preparedState degree.val factors work raw
    WitnessRows polynomial degree.val 0 state.rows state.witnesses ∧
      vectorImage polynomial state.residue = residue polynomial (columnPower 0) := by
  dsimp only
  obtain ⟨layout, initialResidueWidth, _, _⟩ := arena
  let rows := (preparedState degree.val factors work raw).rows
  let witnesses := (preparedState degree.val factors work raw).witnesses
  have width : polynomial.len.val = degree.val + 1 := layout.widthValue
  have rowRoom : degree.val * degree.val ≤ rows.length := layout.rowsRoom
  have witnessRoom : degree.val * (degree.val + 1) ≤ witnesses.length := by
    have bound := layout.witnessesRoom
    change degree.val * polynomial.len.val ≤ witnesses.length at bound
    rwa [width] at bound
  have rowZero : ∀ row < degree.val, ∀ i < degree.val, (matrixRow rows degree.val row)[i]! = 0#u64 := by
    intro row active i inside
    have fits : (row + 1) * degree.val ≤ rows.length :=
      (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt active)).trans rowRoom
    rw [matrix_row_word rows degree.val row i fits inside]
    have global : row * degree.val + i < rows.length := by
      rw [Nat.add_mul, Nat.one_mul] at fits
      omega
    change (zeroWords (prefixSlice factors (degree.val * degree.val)))[row * degree.val + i]! = _
    apply zero_words_word
    simpa only [rows, preparedState, zero_length] using global
  have witnessZero : ∀ row < degree.val, ∀ i < degree.val + 1,
      (matrixRow witnesses (degree.val + 1) row)[i]! = 0#u64 := by
    intro row active i inside
    have fits : (row + 1) * (degree.val + 1) ≤ witnesses.length :=
      (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt active)).trans witnessRoom
    rw [matrix_row_word witnesses (degree.val + 1) row i fits inside]
    have global : row * (degree.val + 1) + i < witnesses.length := by
      rw [Nat.add_mul, Nat.one_mul] at fits
      omega
    change (zeroWords (prefixSlice (tail factors (degree.val * degree.val))
      (degree.val * (degree.val + 1))))[row * (degree.val + 1) + i]! = _
    apply zero_words_word
    simpa only [witnesses, preparedState, zero_length] using global
  refine ⟨⟨Nat.zero_le _, rowRoom, witnessRoom, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro row active i earlier
    exact rowZero row active i (earlier.trans active)
  · intro row active i inside _
    exact witnessZero row active i inside
  · intro row active
    unfold vectorImage witnessImage weightedValue
    have rowFits : (row + 1) * degree.val ≤ rows.length :=
      (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt active)).trans rowRoom
    have witnessFits : (row + 1) * (degree.val + 1) ≤ witnesses.length :=
      (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt active)).trans witnessRoom
    rw [matrix_row_length rows degree.val row rowFits,
      matrix_row_length witnesses (degree.val + 1) row witnessFits]
    have zeroLeft : (∑ i ∈ Finset.range degree.val,
        ((residue polynomial).comp C) (toField (matrixRow rows degree.val row)[i]!.bv) *
          residueX polynomial ^ i) = 0 := by
      apply Finset.sum_eq_zero
      intro i member
      rw [rowZero row active i (Finset.mem_range.mp member)]
      change ((residue polynomial).comp C) (toField 0) * _ = 0
      rw [toField_zero, map_zero, zero_mul]
    have zeroRight : (∑ i ∈ Finset.range (degree.val + 1),
        ((residue polynomial).comp C) (toField (matrixRow witnesses (degree.val + 1) row)[i]!.bv) *
          residue polynomial (columnPower i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i member
      rw [witnessZero row active i (Finset.mem_range.mp member)]
      change ((residue polynomial).comp C) (toField 0) * _ = 0
      rw [toField_zero, map_zero, zero_mul]
    exact zeroLeft.trans zeroRight.symm
  · intro row active
    have fits : (row + 1) * degree.val ≤ rows.length :=
      (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt active)).trans rowRoom
    exact Or.inl ((matrix_row_word rows degree.val row row fits active).symm ▸ rowZero row active row active)
  · have actualWidth : (prefixSlice work degree.val).length = degree.val := by
      change ((zeroWords (prefixSlice work degree.val)).setAtNat 0 1#u64).length = degree.val at initialResidueWidth
      rwa [Slice.setAtNat_length, zero_length] at initialResidueWidth
    change vectorImage polynomial ((zeroWords (prefixSlice work degree.val)).setAtNat 0 1#u64) =
      residue polynomial (columnPower 0)
    rw [vector_image_polynomial, initialized_monomial _ _ _ (by rwa [actualWidth])]
    change residue polynomial (monomial 0 (toField 1)) = residue polynomial (X ^ 0)
    rw [toField_one, ← C_mul_X_pow_eq_monomial, map_one, one_mul]

private theorem yielded_column_shape (iter next : ColumnIter) (column : Usize)
    (yielded : nextColumn iter = .ok (some column, next)) :
    column = iter.start ∧ iter.exhausted = false ∧ column.val ≤ iter.«end».val ∧
    next.«end» = iter.«end» ∧
    (if column.val < iter.«end».val then next.start.val = column.val + 1 else next.exhausted = true) := by
  obtain ⟨⟨option, after⟩, actual, meaning⟩ := RawMulTable.normal_of_spec _ _
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec iter)
  have exactPair : (option, after) = (some column, next) := Result.ok_injective (actual.symm.trans yielded)
  have optionEq : option = some column := congrArg Prod.fst exactPair
  have afterEq : after = next := congrArg Prod.snd exactPair
  subst option after
  dsimp only [WP.uncurry'] at meaning
  by_cases empty : iter.exhausted ∨ iter.«end».val < iter.start.val
  · rw [ite_eq_left empty] at meaning
    exact False.elim (Option.some_ne_none _ meaning.1)
  · rw [ite_eq_right empty] at meaning
    have live : iter.exhausted = false := Bool.eq_false_iff.mpr (fun yes => empty (.inl yes))
    have admitted : iter.start.val ≤ iter.«end».val := Nat.le_of_not_gt (fun greater => empty (.inr greater))
    by_cases before : iter.start.val < iter.«end».val
    · rw [ite_eq_left before] at meaning
      obtain ⟨same, start, ending, _⟩ := meaning
      have columnEq : column = iter.start := Option.some.inj same
      subst column
      exact ⟨rfl, live, admitted, ending, by rwa [ite_eq_left before]⟩
    · rw [ite_eq_right before] at meaning
      obtain ⟨same, _, ending, exhausted⟩ := meaning
      have columnEq : column = iter.start := Option.some.inj same
      subst column
      exact ⟨rfl, live, admitted, ending, by rwa [ite_eq_right before]⟩

private theorem successful_trace_live {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (restores : ColumnRestores) (shape : ColumnShape)
    (iter : ColumnIter) (state : ColumnState) (result : Result ColumnDone)
    (trace : ColumnTrace square kernels restores shape iter state result)
    (output : ColumnDone) (normal : result = .ok output) : iter.exhausted = false := by
  cases trace with
  | exhausted yielded => exact False.elim (fail_not_ok normal)
  | dependent yielded _ _ _ => exact (yielded_column_shape _ _ _ yielded).2.1
  | pivot yielded _ _ _ _ _ => exact (yielded_column_shape _ _ _ yielded).2.1

private theorem selected_nonzero (degree column : Nat) (rows witnesses : Slice U64)
    (fuel row : Nat) (vector witness : Slice U64) (remaining : row + fuel = degree)
    (pivot : Nat) (selected : (pivotSearch degree column rows witnesses fuel row vector witness).2.2 = some pivot) :
    pivot < degree ∧ (pivotSearch degree column rows witnesses fuel row vector witness).1[pivot]! ≠ 0#u64 := by
  induction fuel generalizing row vector witness with
  | zero => contradiction
  | succ fuel ih =>
    by_cases skip : vector[row]! = 0#u64
    · simp only [pivotSearch, pivotRow, skip, ite_true] at selected ⊢
      exact ih (row + 1) vector witness (by omega) selected
    · by_cases vacant : rows[row * degree + row]! = 0#u64
      · simp only [pivotSearch, pivotRow, ite_eq_right skip, vacant, ite_true, Option.some.injEq] at selected ⊢
        subst pivot
        exact ⟨by omega, skip⟩
      · simp only [pivotSearch, pivotRow, ite_eq_right skip, ite_eq_right vacant] at selected ⊢
        exact ih (row + 1) _ _ (by omega) selected

private theorem initial_column_witness (modulus : Slice U64) (degree : Nat) (column : Usize)
    (residueWords witness : Slice U64) (columnRoom : column.val ≤ degree)
    (residueWidth : residueWords.length = degree) (witnessWidth : witness.length = degree + 1)
    (image : vectorImage modulus residueWords = residue modulus (columnPower column.val)) :
    ColumnWitness modulus degree column.val residueWords (initialWitness column witness) := by
  have room : column.val < witness.length := by rw [witnessWidth]; exact Nat.lt_succ_of_le columnRoom
  refine ⟨residueWidth, by simp only [initialWitness, Slice.setAtNat_length, zero_length, witnessWidth],
    ?_, ?_, ?_⟩
  · rw [image, initial_witness_image _ _ _ room]
  · rw [initial_witness_word _ _ _ room room, ite_eq_left rfl]
  · intro i inside later
    rw [initial_witness_word _ _ _ (by rwa [witnessWidth]) room, ite_eq_right (by omega)]

/-- Every successful operational trace returns a monic packed witness of
the reported leading column degree and divisible by the original modulus.
The proof propagates the quotient relation across the exact native stores
and original full-width modular-square continuation. -/
theorem successful_trace_witness {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (scaleLaw : TimesXMod.ExactScaleXor kernels) (restores : ColumnRestores) (shape : ColumnShape)
    (fullSquare : AffineSplitter.FullSquareLaw square kernels shape.polynomial shape.table shape.degree.val)
    (iter : ColumnIter) (state : ColumnState) (result : Result ColumnDone)
    (trace : ColumnTrace square kernels restores shape iter state result) :
    ∀ (_ending : iter.«end» = shape.degree),
      WitnessRows shape.polynomial shape.degree.val iter.start.val state.rows state.witnesses →
      vectorImage shape.polynomial state.residue = residue shape.polynomial (columnPower iter.start.val) →
      2 * shape.degree.val < state.raw.length →
      ∀ output : ColumnDone, result = .ok output →
      ∃ column : Nat, column ≤ shape.degree.val ∧ output.1.val = column + 1 ∧
        let polynomial := packedWitness (prefixSlice output.2.2.1 output.1.val)
        polynomial.Monic ∧ polynomial.natDegree = columnExponent column ∧
          slicePolynomial shape.polynomial ∣ polynomial := by
  induction trace with
  | @exhausted iter next state yielded =>
    intro _ _ _ _ output normal
    exact False.elim (fail_not_ok normal)
  | @dependent iter next state column length yielded ready dependent lengthValue =>
    intro ending rows image _ output normal
    obtain ⟨columnEq, _, admitted, _, _⟩ := yielded_column_shape iter next column yielded
    subst column
    obtain ⟨actualLength, affine, factors, work, exactCall, lenValue, monic, degree, divisible⟩ :=
      native_dependent_column_witness square kernels scaleLaw restores shape iter next state iter.start
        ready yielded rows image dependent
    obtain ⟨refinedLength, refinedValue, modeled⟩ :=
      dependent_column_refines square kernels scaleLaw restores shape iter next state iter.start ready yielded dependent
    have lengthEq : refinedLength = length := UScalar.eq_of_val_eq (refinedValue.trans lengthValue.symm)
    subst refinedLength
    have exactModel : columnBody square kernels restores shape iter state =
      .ok (.done (dependentOutput restores shape state iter.start length)) := modeled
    have same := Result.ok_injective (exactModel.symm.trans exactCall)
    have exactOutput : dependentOutput restores shape state iter.start length =
        (actualLength, factors, affine, work, state.raw) := by
      cases same
      rfl
    have outputEq := Result.ok_injective normal
    rw [exactOutput] at outputEq
    subst output
    refine ⟨iter.start.val, ?_, lenValue, monic, degree, divisible⟩
    rwa [ending] at admitted
  | @pivot iter next state column advanced result yielded ready minimum _ stored tail ih =>
    intro ending rows image rawRoom output normal
    obtain ⟨columnEq, _, admitted, nextEnd, transition⟩ := yielded_column_shape iter next column yielded
    subst column
    have live := successful_trace_live square kernels restores shape next advanced result tail output normal
    by_cases before : iter.start.val < iter.«end».val
    · rw [ite_eq_left before] at transition
      have active : iter.start.val < shape.degree.val := by rwa [ending] at before
      obtain ⟨layout, residueWidth, _⟩ := ready
      have initial := initial_column_witness shape.polynomial shape.degree.val iter.start state.residue state.witness
        layout.columnRoom residueWidth (layout.witnessWidth.trans layout.widthValue) image
      obtain ⟨vector, witness, pivot, search, writtenRows, writtenWitnesses, _, residueStep⟩ := stored
      have selected : (searchedColumn shape state iter.start).2.2 = some pivot.val := by rw [search]
      have nonzero := selected_nonzero shape.degree.val iter.start.val state.rows state.witnesses
        shape.degree.val 0 state.residue (initialWitness iter.start state.witness) (by simp) pivot.val selected
      change pivot.val < shape.degree.val ∧ (searchedColumn shape state iter.start).1[pivot.val]! ≠ 0#u64 at nonzero
      rw [search] at nonzero
      obtain ⟨pivotActive, pivotNonzero⟩ := nonzero
      have below := selected_pivot_below_zero shape.polynomial shape.degree.val iter.start.val state.rows state.witnesses
        rows shape.degree.val 0 state.residue (initialWitness iter.start state.witness)
        (by simp) initial (by intro i impossible; omega) pivot.val selected
      change ∀ i < pivot.val, (searchedColumn shape state iter.start).1[i]! = 0#u64 at below
      rw [search] at below
      have paired := (pivot_search_witness shape.polynomial shape.degree.val iter.start.val
        state.rows state.witnesses rows shape.degree.val 0 state.residue (initialWitness iter.start state.witness)
        (by simp) initial (by intro i impossible; omega)).1
      change ColumnWitness shape.polynomial shape.degree.val iter.start.val
        (searchedColumn shape state iter.start).1 (searchedColumn shape state iter.start).2.1 at paired
      rw [search] at paired
      have nextRows := store_pivot_witness_rows shape.polynomial shape.degree.val iter.start.val pivot.val
        state.rows state.witnesses vector witness rows paired active pivotActive below pivotNonzero
      rw [layout.widthValue] at writtenWitnesses
      rw [← writtenRows, ← writtenWitnesses, ← transition] at nextRows
      obtain ⟨nextImage, nextRawWidth⟩ := continued_residue_image square kernels shape state iter.start vector
        advanced.residue advanced.vector advanced.raw active minimum residueWidth paired.vectorWidth rawRoom fullSquare
        image residueStep
      rw [← transition] at nextImage
      exact ih (nextEnd.trans ending) nextRows nextImage (by rwa [nextRawWidth]) output normal
    · rw [ite_eq_right before] at transition
      rw [live] at transition
      contradiction

end BulksketchBridge.AffineMultiple
