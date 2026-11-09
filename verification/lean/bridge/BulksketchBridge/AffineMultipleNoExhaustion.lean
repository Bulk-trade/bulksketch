import BulksketchBridge.AffineMultipleWrapper

namespace BulksketchBridge.AffineMultiple

open Aeneas Aeneas.Std Aeneas.Std.WP Algebra.Gf64 DenseCoefficient RebuiltLfsr BmEntry MutableZip
open bulksketch.backend.contract bulksketch.types bulksketch.decode.affine
open ClosedLeaf (region)

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem vector_tail_head (vector : Slice U64) (row : Nat) (inside : row < vector.length) :
    (tail vector row)[(0 : Nat)]! = vector[row]! := by
  simp only [tail, Slice.getElem!_Nat_eq, Slice.from_val]
  have active : (0 : Nat) < (vector.val.drop row).length := by
    rw [List.length_drop]
    change 0 < vector.length - row
    omega
  rw [← List.Inhabited_getElem_eq_getElem! _ _ active, List.getElem_drop]
  exact List.Inhabited_getElem_eq_getElem! _ _ inside

/-- The actual normalization model makes the selected vacant diagonal one
    and preserves every other diagonal. This is the local counting step
    for proving that the outer iterator cannot exhaust. -/
theorem normalized_diagonal (degree row : Nat) (rows vector : Slice U64)
    (active : row < degree) (rowsRoom : degree * degree ≤ rows.length)
    (vectorWidth : vector.length = degree) (nonzero : vector[row]! ≠ 0#u64)
    (index : Nat) (inside : index < degree) :
    (normalizedRows degree row rows vector (DenseDivision.divisorInverse vector[row]!))[index * degree + index]! =
      if index = row then 1#u64 else rows[index * degree + index]! := by
  let start := row * degree + row
  let stop := (row + 1) * degree
  let patch := mapFrom (region rows start stop) (tail vector row)
    (scaleWord (DenseDivision.divisorInverse vector[row]!)) 0
  have stopFits : stop ≤ rows.length :=
    (Nat.mul_le_mul_right degree (by omega : row + 1 ≤ degree)).trans rowsRoom
  have width : stop - start = degree - row := by
    unfold start stop
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have patchWidth : patch.length = degree - row := by
    change (mapFrom (region rows start stop) (tail vector row)
      (scaleWord (DenseDivision.divisorInverse vector[row]!)) 0).length = _
    rw [mapFrom_length, ClosedLeaf.region_length _ _ _ stopFits, width]
  have filled : start + patch.val.length = stop := by
    have startFits : start ≤ stop := by unfold start stop; rw [Nat.add_mul, Nat.one_mul]; omega
    change start + patch.length = stop
    omega
  change (rows.setSlice! start patch.val)[index * degree + index]! = _
  by_cases chosen : index = row
  · subst index
    change (rows.setSlice! start patch.val)[start]! = _
    rw [ite_eq_left rfl, Slice.setSlice!_getElem!_middle _ _ _ _ (by
      have room : 0 < patch.val.length := by change 0 < patch.length; omega
      omega), Nat.sub_self]
    have head : (0 : Nat) < (region rows start stop).length := by
      rw [ClosedLeaf.region_length _ _ _ stopFits, width]
      omega
    rw [← Slice.getElem!_Nat_eq]
    unfold patch
    rw [mapFrom_word _ _ _ _ _ head, ite_eq_left (Nat.zero_le _), vector_tail_head vector row (by omega)]
    unfold scaleWord
    apply U64.bv_eq_imp_eq
    apply toField_injective
    change toField (multiplyWord vector[row]!.bv (DenseDivision.divisorInverse vector[row]!).bv) = _
    rw [toField_mul, mul_comm, show toField (1#u64).bv = 1 from toField_one]
    exact DenseDivision.divisor_inverse_law _ nonzero
  · rw [ite_eq_right chosen]
    by_cases before : index < row
    · have old := Nat.mul_le_mul_right degree before.le
      exact Slice.setSlice!_getElem!_prefix _ _ _ _ (by unfold start; omega)
    · have after : stop ≤ index * degree := Nat.mul_le_mul_right degree (by omega : row + 1 ≤ index)
      exact Slice.setSlice!_getElem!_suffix _ _ _ _ (by omega)


def occupiedRows (degree : Nat) (rows : Slice U64) : Finset Nat :=
  (Finset.range degree).filter (fun index => rows[index * degree + index]! ≠ 0#u64)

theorem occupied_after (degree row : Nat) (rows vector : Slice U64)
    (active : row < degree) (rowsRoom : degree * degree ≤ rows.length)
    (vectorWidth : vector.length = degree) (nonzero : vector[row]! ≠ 0#u64)
    (vacant : rows[row * degree + row]! = 0#u64) :
    (occupiedRows degree (normalizedRows degree row rows vector (DenseDivision.divisorInverse vector[row]!))).card =
      (occupiedRows degree rows).card + 1 := by
  have changeSet :
      occupiedRows degree (normalizedRows degree row rows vector (DenseDivision.divisorInverse vector[row]!)) =
        insert row (occupiedRows degree rows) := by
    ext index
    simp only [occupiedRows, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    by_cases fits : index < degree
    · rw [normalized_diagonal degree row rows vector active rowsRoom vectorWidth nonzero index fits]
      by_cases same : index = row
      · simp [same, active]
      · simp [same, fits]
    · have different : index ≠ row := by omega
      simp [fits, different]
  rw [changeSet, Finset.card_insert_of_notMem]
  intro present
  exact (Finset.mem_filter.mp present).2 vacant

private theorem column_measure (iter next : ColumnIter) (option : Option Usize)
    (normal : nextColumn iter = .ok (option, next)) :
    match option with
    | none => columnsLeft iter = 0
    | some _ => columnsLeft iter = columnsLeft next + 1 := by
  obtain ⟨⟨actual, following⟩, observed, meaning⟩ := RawMulTable.normal_of_spec _ _
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec iter)
  have same := Result.ok_injective (observed.symm.trans normal)
  cases same
  dsimp only [WP.uncurry'] at meaning
  by_cases empty : iter.exhausted ∨ iter.«end».val < iter.start.val
  · rw [ite_eq_left empty] at meaning
    obtain ⟨rfl, _⟩ := meaning
    rcases empty with exhausted | passed
    · simp [columnsLeft, exhausted]
    · simp only [columnsLeft]
      split <;> omega
  · rw [ite_eq_right empty] at meaning
    have inside : iter.start.val ≤ iter.«end».val :=
      Nat.le_of_not_gt (fun greater => empty (.inr greater))
    have live : iter.exhausted = false := Bool.eq_false_iff.mpr (fun yes => empty (.inl yes))
    by_cases before : iter.start.val < iter.«end».val
    · rw [ite_eq_left before] at meaning
      obtain ⟨rfl, advanced, ending, liveNext⟩ := meaning
      simp only [columnsLeft, live, liveNext, Bool.false_eq_true, ite_false, advanced, ending]
      omega
    · rw [ite_eq_right before] at meaning
      obtain ⟨rfl, _, _, exhaustedNext⟩ := meaning
      simp only [columnsLeft, live, exhaustedNext, Bool.false_eq_true, ite_false, ite_true]
      omega

private theorem pivot_model_vacant {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (scale : TimesXMod.ExactScaleXor kernels) (shape : ColumnShape) (state : ColumnState)
    (column row : Usize) (ready : columnReady shape column state) (vector witness : Slice U64)
    (search : searchedColumn shape state column = (vector, witness, some row.val)) :
    row.val < shape.degree.val ∧ state.rows[row.val * shape.degree.val + row.val]! = 0#u64 ∧
      vector.length = shape.degree.val ∧ vector[row.val]! ≠ 0#u64 := by
  have layout := ready.1
  have setup : PivotLayout shape.degree shape.width column state.rows state.witnesses
      state.residue (initialWitness column state.witness) :=
    ⟨layout.widthValue, layout.columnRoom, layout.rowsRoom, layout.witnessesRoom, ready.2.1,
      by rw [initialWitness, Slice.setAtNat_length, zero_length]; exact layout.witnessWidth⟩
  obtain ⟨actualVector, actualWitness, selected, _, model, fitted, found⟩ :=
    pivot_search_refines kernels scale shape.degree shape.width column state.rows state.witnesses
      state.residue (initialWitness column state.witness) ⟨0#usize, shape.degree⟩ setup rfl
  have same : (actualVector, actualWitness, selected.map UScalar.val) = (vector, witness, some row.val) := by
    rw [← search]
    simpa only [searchedColumn, show (0#usize).val = 0 from rfl, Nat.sub_zero] using model.symm
  cases selected with
  | none => simp at same
  | some index =>
    obtain ⟨vectorEq, _, indexValue⟩ := by simpa only [Prod.mk.injEq, Option.map_some, Option.some.injEq] using same
    obtain ⟨_, inside, vacant, nonzero⟩ := found index rfl
    rw [indexValue] at inside vacant nonzero
    rw [vectorEq] at nonzero
    exact ⟨inside, vacant, vectorEq ▸ fitted.vectorWidth, nonzero⟩

/-- There are degree plus one columns and only degree vacant diagonal
    slots. A fully checked original trace must find a dependent column. -/
theorem column_trace_returns {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (scale : TimesXMod.ExactScaleXor kernels)
    (restores : ColumnRestores) (shape : ColumnShape) (iter : ColumnIter) (state : ColumnState)
    (result : Result ColumnDone) (trace : ColumnTrace square kernels restores shape iter state result)
    (room : shape.degree.val < (occupiedRows shape.degree.val state.rows).card + columnsLeft iter)
    (factorsLength workLength : Nat)
    (factorFrame : ∀ rows witnesses, (restores.factors (rows, restores.witnesses witnesses)).length = factorsLength)
    (workFrame : ∀ residue vector witness,
      (restores.work (residue, restores.vector (vector, restores.witness witness))).length = workLength) :
    ∃ output : ColumnDone, result = .ok output ∧
      0 < output.1.val ∧ output.1.val ≤ shape.degree.val + 1 ∧
      output.2.1.length = factorsLength ∧ output.2.2.1.length = shape.affine.length ∧
      output.2.2.2.1.length = workLength := by
  induction trace with
  | @exhausted iter next state ended =>
    have noColumns := column_measure iter next none ended
    have occupiedLimit : (occupiedRows shape.degree.val state.rows).card ≤ shape.degree.val :=
      (Finset.card_filter_le ..).trans (by rw [Finset.card_range])
    change columnsLeft iter = 0 at noColumns
    omega
  | @dependent iter next state column length yielded ready _ lengthValue =>
    rcases searched : searchedColumn shape state column with ⟨vector, witness, option⟩
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [dependentOutput, searched, lengthValue]
      omega
    · simp only [dependentOutput, searched, lengthValue]
      exact Nat.add_le_add_right ready.1.columnRoom 1
    · simp only [dependentOutput, searched, factorFrame]
    · simp only [dependentOutput, searched, restore_length]
    · simp only [dependentOutput, searched, workFrame]
  | @pivot iter next state column advanced result yielded ready _ _ stored rest ih =>
    obtain ⟨vector, witness, row, search, written, _⟩ := stored
    obtain ⟨inside, vacant, vectorWidth, nonzero⟩ :=
      pivot_model_vacant kernels scale shape state column row ready vector witness search
    have count := occupied_after shape.degree.val row.val state.rows vector inside ready.1.rowsRoom
      vectorWidth nonzero vacant
    have nextMeasure := column_measure iter next (some column) yielded
    change columnsLeft iter = columnsLeft next + 1 at nextMeasure
    apply ih
    rw [written, count]
    omega

def ActualNativeMultipleReturns : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (polynomial table factors affine work : Slice U64) (raw : Slice RawProduct),
    TimesXMod.ExactScaleXor kernels → DenseDivRem.MulWordLaw kernels →
    BmTerminal.NativeInverse kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    DenseReducerSquare.SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    4 ≤ polynomial.length → polynomial[polynomial.length - 1]! = 1#u64 →
    table.length = (polynomial.length - 1) * ((polynomial.length - 1) / 2) →
    DenseReducerAlgebra.CorrectTable polynomial table (polynomial.length - 1) →
    DenseReducerSquare.BackendSquareLaw kernels polynomial table (polynomial.length - 1) →
    Layout (polynomial.length - 1) factors.length work.length affine.length →
    2 * (polynomial.length - 1) < raw.length →
    ∃ output : ColumnDone,
      multiple RootTrace.nativeSquare RootSetup.gf64Dictionary kernels polynomial table factors affine work raw = .ok output ∧
      0 < output.1.val ∧ output.1.val ≤ polynomial.length ∧
      output.2.1.length = factors.length ∧ output.2.2.1.length = affine.length ∧
      output.2.2.2.1.length = work.length

theorem native_multiple_returns : ActualNativeMultipleReturns := by
  intro K kernels polynomial table factors affine work raw scale mul inverse rawMul square reduce
    minimum monic tableLen correct backend layout scratchRoom
  obtain ⟨degree, result, degreeValue, trace, normal⟩ :=
    native_multiple_refines kernels polynomial table factors affine work raw scale mul inverse rawMul square
      reduce minimum monic tableLen correct backend layout scratchRoom
  obtain ⟨output, finished, positive, size, factorFrame, affineFrame, workFrame⟩ :=
    column_trace_returns RootTrace.nativeSquare kernels scale
    (preparedRestores degree.val factors work) (preparedShape degree polynomial table affine)
    ⟨0#usize, degree, false⟩ (preparedState degree.val factors work raw) result trace (by
      simp only [preparedShape, columnsLeft, Bool.false_eq_true, ite_false]
      change degree.val <
        (occupiedRows degree.val (preparedState degree.val factors work raw).rows).card + (degree.val + 1 - 0)
      omega) factors.length work.length
      (fun rows witnesses => splitBack_length factors _ _)
      (fun residue vector witness => splitBack_length work _ _)
  refine ⟨output, normal.trans finished, positive, ?_, factorFrame, affineFrame, workFrame⟩
  change output.1.val ≤ degree.val + 1 at size
  omega


end BulksketchBridge.AffineMultiple
