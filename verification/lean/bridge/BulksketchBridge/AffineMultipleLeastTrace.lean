import BulksketchBridge.AffineMultipleIndependence

namespace BulksketchBridge.AffineMultiple

open Aeneas Aeneas.Std Result Polynomial Algebra.Gf64 DenseReducerAlgebra SliceKernels
open DenseCoefficient RebuiltLfsr BmEntry DenseMulConvolutionSpec DenseReducerSquare
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

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

private theorem selected_pivot_facts (degree column : Nat) (rows witnesses : Slice U64)
    (fuel row : Nat) (vector witness : Slice U64) (remaining : row + fuel = degree)
    (pivot : Nat) (selected : (pivotSearch degree column rows witnesses fuel row vector witness).2.2 = some pivot) :
    pivot < degree ∧ rows[pivot * degree + pivot]! = 0#u64 ∧
      (pivotSearch degree column rows witnesses fuel row vector witness).1[pivot]! ≠ 0#u64 := by
  induction fuel generalizing row vector witness with
  | zero => contradiction
  | succ fuel ih =>
    by_cases skip : vector[row]! = 0#u64
    · simp only [pivotSearch, pivotRow, skip, ite_true] at selected ⊢
      exact ih (row + 1) vector witness (by omega) selected
    · by_cases vacant : rows[row * degree + row]! = 0#u64
      · simp only [pivotSearch, pivotRow, ite_eq_right skip, vacant, ite_true, Option.some.injEq] at selected ⊢
        subst pivot
        exact ⟨by omega, vacant, skip⟩
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

/-- The exact trace increases the occupied pivot count by one after each
successful column, so the prior columns are independent at the first
dependent return. -/
theorem successful_trace_prefix_independent {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (restores : ColumnRestores) (shape : ColumnShape)
    (fullSquare : AffineSplitter.FullSquareLaw square kernels shape.polynomial shape.table shape.degree.val)
    (degreeEq : (slicePolynomial shape.polynomial).natDegree = shape.degree.val)
    (monic : (slicePolynomial shape.polynomial).Monic)
    (iter : ColumnIter) (state : ColumnState) (result : Result ColumnDone)
    (trace : ColumnTrace square kernels restores shape iter state result) :
    ∀ (_ending : iter.«end» = shape.degree),
      WitnessRows shape.polynomial shape.degree.val iter.start.val state.rows state.witnesses →
      vectorImage shape.polynomial state.residue = residue shape.polynomial (columnPower iter.start.val) →
      2 * shape.degree.val < state.raw.length →
      (occupiedRows shape.degree.val state.rows).card = iter.start.val →
      ∀ output : ColumnDone, result = .ok output →
        ∃ column : Nat, output.1.val = column + 1 ∧ PrefixIndependent shape.polynomial column := by
  induction trace with
  | @exhausted iter next state yielded =>
    intro _ _ _ _ _ output normal
    exact False.elim (fail_not_ok normal)
  | @dependent iter next state column length yielded _ _ lengthValue =>
    intro ending rows _ _ count output normal
    obtain ⟨columnEq, _, _, _, _⟩ := yielded_column_shape iter next column yielded
    subst column
    have resultLength : (dependentOutput restores shape state iter.start length).1 = length := by
      unfold dependentOutput
      rcases searchedColumn shape state iter.start with ⟨v, w, p⟩
      rfl
    have eq := Result.ok_injective normal
    refine ⟨iter.start.val, ?_, prefix_independent_of_occupied_count
      shape.polynomial shape.degree.val iter.start.val state.rows state.witnesses rows degreeEq monic count⟩
    rw [← eq, resultLength, lengthValue]
  | @pivot iter next state column advanced result yielded ready minimum _ stored tail ih =>
    intro ending rows image rawRoom count output normal
    obtain ⟨columnEq, _, _, nextEnd, transition⟩ := yielded_column_shape iter next column yielded
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
      have facts := selected_pivot_facts shape.degree.val iter.start.val state.rows state.witnesses
        shape.degree.val 0 state.residue (initialWitness iter.start state.witness) (by simp) pivot.val selected
      change pivot.val < shape.degree.val ∧ state.rows[pivot.val * shape.degree.val + pivot.val]! = 0#u64 ∧
        (searchedColumn shape state iter.start).1[pivot.val]! ≠ 0#u64 at facts
      rw [search] at facts
      obtain ⟨pivotActive, vacant, pivotNonzero⟩ := facts
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
      have occupied := occupied_after shape.degree.val pivot.val state.rows vector
        pivotActive layout.rowsRoom paired.vectorWidth pivotNonzero vacant
      rw [← writtenRows, count, ← transition] at occupied
      obtain ⟨nextImage, nextRawWidth⟩ := continued_residue_image square kernels shape state iter.start vector
        advanced.residue advanced.vector advanced.raw active minimum residueWidth paired.vectorWidth rawRoom fullSquare
        image residueStep
      rw [← transition] at nextImage
      exact ih (nextEnd.trans ending) nextRows nextImage (by rwa [nextRawWidth]) occupied output normal
    · rw [ite_eq_right before] at transition
      rw [live] at transition
      contradiction

private theorem initial_occupied_count (degree : Usize) (factors work : Slice U64)
    (raw : Slice bulksketch.types.RawProduct)
    (room : degree.val * degree.val ≤ factors.length) :
    (occupiedRows degree.val (preparedState degree.val factors work raw).rows).card = 0 := by
  have none : occupiedRows degree.val (preparedState degree.val factors work raw).rows = ∅ := by
    ext i
    simp only [occupiedRows, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
    rintro ⟨inside, nonzero⟩
    have ⟨diagonal, ending, _⟩ := row_window inside
    apply nonzero
    change (zeroWords (prefixSlice factors (degree.val * degree.val)))[i * degree.val + i]! = 0#u64
    apply zero_words_word
    rw [prefix_length, Nat.min_eq_left room]
    omega
  rw [none, Finset.card_empty]

private theorem modulus_degree_and_monic (polynomial : Slice U64) (positive : 0 < polynomial.length)
    (leading : polynomial[polynomial.length - 1]! = 1#u64) :
    (slicePolynomial polynomial).natDegree = polynomial.length - 1 ∧ (slicePolynomial polynomial).Monic := by
  have upper : (slicePolynomial polynomial).natDegree ≤ polynomial.length - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i higher
    rw [slicePolynomial_coeff, ite_eq_right (by omega)]
  have one : (slicePolynomial polynomial).coeff (polynomial.length - 1) = 1 := by
    rw [slicePolynomial_coeff, ite_eq_left (by omega), leading]
    exact toField_one
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero upper (by rw [one]; exact one_ne_zero),
    monic_of_natDegree_le_of_coeff_eq_one _ upper one⟩

/-- The actual successful native wrapper returns a least-degree nonzero
packed affine polynomial divisible by its monic input. -/
def ActualNativeReturnedLeast : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (polynomial table factors affine work : Slice U64) (raw : Slice bulksketch.types.RawProduct),
    TimesXMod.ExactScaleXor kernels → DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    4 ≤ polynomial.length → polynomial[polynomial.length - 1]! = 1#u64 →
    table.length = (polynomial.length - 1) * ((polynomial.length - 1) / 2) →
    CorrectTable polynomial table (polynomial.length - 1) →
    BackendSquareLaw kernels polynomial table (polynomial.length - 1) →
    Layout (polynomial.length - 1) factors.length work.length affine.length →
    2 * (polynomial.length - 1) < raw.length →
    ∀ output : ColumnDone,
    bulksketch.decode.affine.multiple RootTrace.nativeSquare RootSetup.gf64Dictionary kernels
      polynomial table factors affine work raw = .ok output →
    let witness := packedWitness (prefixSlice output.2.2.1 output.1.val)
    witness.Monic ∧ slicePolynomial polynomial ∣ witness ∧
      ∀ other : Slice U64, packedWitness other ≠ 0 →
        slicePolynomial polynomial ∣ packedWitness other →
        witness.natDegree ≤ (packedWitness other).natDegree

theorem native_multiple_returned_packed_least : ActualNativeReturnedLeast := by
  intro K kernels polynomial table factors affine work raw scale mul inverse rawMul square reduce
    minimum monic tableLength correct backend layout rawRoom output successful
  obtain ⟨column, bounded, length, witnessMonic, witnessDegree, divides⟩ :=
    native_multiple_returned_packed_witness kernels polynomial table factors affine work raw scale mul inverse
      rawMul square reduce minimum monic tableLength correct backend layout rawRoom output successful
  obtain ⟨degree, result, degreeValue, trace, normal⟩ :=
    native_multiple_refines kernels polynomial table factors affine work raw scale mul inverse rawMul square reduce
      minimum monic tableLength correct backend layout rawRoom
  obtain ⟨preparedDegree, preparedValue, arena, _⟩ :=
    multiple_prelude_refines RootTrace.nativeSquare kernels polynomial table factors affine work raw layout rawRoom
  have same : preparedDegree = degree := UScalar.eq_of_val_eq (preparedValue.trans degreeValue.symm)
  subst preparedDegree
  have positive : 0 < degree.val := by rw [degreeValue]; have := layout.degree_min; omega
  obtain ⟨rows, image⟩ := prepared_witness_rows degree polynomial table factors affine work raw arena positive
  obtain ⟨modDegree, modMonic⟩ := modulus_degree_and_monic polynomial (by omega) monic
  have full := AffineSplitter.native_full_square kernels rawMul square reduce polynomial table (polynomial.length - 1)
    minimum (by omega) monic tableLength correct backend
  have fullSquare : AffineSplitter.FullSquareLaw RootTrace.nativeSquare kernels
      (preparedShape degree polynomial table affine).polynomial (preparedShape degree polynomial table affine).table
      (preparedShape degree polynomial table affine).degree.val := by
    simpa only [preparedShape, degreeValue] using full
  have rawFits : 2 * degree.val < (preparedState degree.val factors work raw).raw.length := by
    simpa only [preparedState, degreeValue] using rawRoom
  have factorsRoom : degree.val * degree.val ≤ factors.length := by
    rw [degreeValue]
    have := layout.factor_room
    omega
  have count := initial_occupied_count degree factors work raw factorsRoom
  obtain ⟨actual, actualLength, independent⟩ := successful_trace_prefix_independent RootTrace.nativeSquare kernels
    (preparedRestores degree.val factors work) (preparedShape degree polynomial table affine)
    fullSquare (by simpa only [preparedShape, degreeValue] using modDegree) modMonic
    ⟨0#usize, degree, false⟩ (preparedState degree.val factors work raw) result trace rfl rows image rawFits
    count output (normal.symm.trans successful)
  have sameColumn : actual = column := by omega
  subst actual
  refine ⟨witnessMonic, divides, ?_⟩
  intro other nonzero multiple
  rw [witnessDegree]
  exact packed_degree_lower_bound polynomial other column independent nonzero multiple

end BulksketchBridge.AffineMultiple
