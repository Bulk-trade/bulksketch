import BulksketchBridge.AffineMultiplePivot
import BulksketchBridge.AffineMultipleNormalization
import BulksketchBridge.ReconstructionLoop
import BulksketchBridge.DenseDivRemCursor

namespace BulksketchBridge.AffineMultiple

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.backend.contract bulksketch.decode.affine bulksketch.types
open DenseCoefficient RebuiltLfsr BmEntry
open ClosedLeaf (region)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

structure ColumnRestores where
  factors : Slice U64 × Slice U64 → Slice U64
  witnesses : Slice U64 → Slice U64
  work : Slice U64 × Slice U64 → Slice U64
  vector : Slice U64 × Slice U64 → Slice U64
  witness : Slice U64 → Slice U64

structure ColumnShape where
  degree : Usize
  width : Usize
  polynomial : Slice U64
  table : Slice U64
  affine : Slice U64

structure ColumnState where
  raw : Slice RawProduct
  rows : Slice U64
  witnesses : Slice U64
  residue : Slice U64
  vector : Slice U64
  witness : Slice U64

abbrev ColumnIter := core.ops.range.RangeInclusive Usize
abbrev ColumnDone := Usize × Slice U64 × Slice U64 × Slice U64 × Slice RawProduct
abbrev ColumnContinue := ColumnIter × Slice RawProduct × Slice U64 × Slice U64 × Slice U64 × Slice U64 × Slice U64

def columnContinue (iter : ColumnIter) (state : ColumnState) : ColumnContinue :=
  (iter, state.raw, state.rows, state.witnesses, state.residue, state.vector, state.witness)

def columnBody {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (restores : ColumnRestores) (shape : ColumnShape)
    (iter : ColumnIter) (state : ColumnState) : Result (ControlFlow ColumnContinue ColumnDone) :=
  multiple_loop0.body square RootSetup.gf64Dictionary kernels restores.factors restores.witnesses
    restores.work restores.vector restores.witness shape.polynomial shape.table shape.affine shape.degree
    shape.width iter state.raw state.rows state.witnesses state.residue state.vector state.witness

def initialWitness (column : Usize) (witness : Slice U64) : Slice U64 :=
  (zeroWords witness).setAtNat column.val 1#u64

def columnReady (shape : ColumnShape) (column : Usize) (state : ColumnState) : Prop :=
  PivotLayout shape.degree shape.width column state.rows state.witnesses state.vector state.witness ∧
    state.residue.length = shape.degree.val ∧ column.val < shape.affine.length

def nextColumn (iter : ColumnIter) : Result (Option Usize × ColumnIter) :=
  core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepUsize iter

theorem exhausted_columns {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (restores : ColumnRestores) (shape : ColumnShape)
    (iter next : ColumnIter) (state : ColumnState)
    (exhausted : nextColumn iter = .ok (none, next)) :
    columnBody square kernels restores shape iter state = .fail .panic := by
  unfold nextColumn at exhausted
  simp only [columnBody, multiple_loop0.body, exhausted, bind_ok]
  rfl

/-- A column returns the first dependent witness with exact prefix and scratch
writeback when the checked pivot search has no remaining pivot. -/
theorem dependent_column_refines {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (law : TimesXMod.ExactScaleXor kernels)
    (restores : ColumnRestores) (shape : ColumnShape) (iter next : ColumnIter) (state : ColumnState)
    (column : Usize) (ready : columnReady shape column state)
    (yielded : nextColumn iter = .ok (some column, next))
    (dependent : (pivotSearch shape.degree.val column.val state.rows state.witnesses
      shape.degree.val 0 state.residue (initialWitness column state.witness)).2.2 = none) :
    ∃ length : Usize,
      length.val = column.val + 1 ∧
      let (vector, witness, _) := pivotSearch shape.degree.val column.val state.rows state.witnesses
        shape.degree.val 0 state.residue (initialWitness column state.witness)
      columnBody square kernels restores shape iter state = .ok (.done
        (length, restores.factors (state.rows, restores.witnesses state.witnesses),
          restorePrefix shape.affine (prefixSlice witness (column.val + 1)),
          restores.work (state.residue, restores.vector (vector, restores.witness witness)), state.raw)) := by
  obtain ⟨layout, residueWidth, affineRoom⟩ := ready
  have witnessRoom : column.val < state.witness.length := by
    rw [layout.witnessWidth, layout.widthValue]
    exact Nat.lt_succ_of_le layout.columnRoom
  have initialLength : (initialWitness column state.witness).length = shape.width.val := by
    simp only [initialWitness, Slice.setAtNat_length, zero_length, layout.witnessWidth]
  have initialLayout : PivotLayout shape.degree shape.width column state.rows state.witnesses
      state.residue (initialWitness column state.witness) :=
    ⟨layout.widthValue, layout.columnRoom, layout.rowsRoom, layout.witnessesRoom, residueWidth, initialLength⟩
  obtain ⟨vector, witness, pivot, run, model, finalLayout, _⟩ :=
    pivot_search_refines kernels law shape.degree shape.width column state.rows state.witnesses
      state.residue (initialWitness column state.witness) ⟨0#usize, shape.degree⟩ initialLayout rfl
  have modelExact : pivotSearch shape.degree.val column.val state.rows state.witnesses
      shape.degree.val 0 state.residue (initialWitness column state.witness) =
      (vector, witness, pivot.map UScalar.val) := by
    simpa only [show (0#usize).val = 0 by decide, Nat.sub_zero] using model
  have noPivot : pivot = none := by
    rw [modelExact] at dependent
    cases pivot
    · rfl
    · contradiction
  rw [noPivot] at run modelExact
  have vectorCopy := ClosedLeaf.copy_normal state.vector state.residue (layout.vectorWidth.trans residueWidth.symm)
  have witnessUpdate := Reconstruction.update_normal (zeroWords state.witness) column 1#u64 (by
    rw [zero_length]
    exact witnessRoom)
  have finalWitnessRoom : column.val < witness.length := by
    rw [finalLayout.witnessWidth, layout.widthValue]
    exact Nat.lt_succ_of_le layout.columnRoom
  have cutAffine := inclusive_prefix shape.affine column affineRoom
  have cutWitness := ClosedLeaf.inclusive_prefix_normal witness column finalWitnessRoom
  have same : (prefixSlice shape.affine (column.val + 1)).length =
      (prefixSlice witness (column.val + 1)).length := by
    rw [prefix_length, prefix_length, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
  have copied := ClosedLeaf.copy_normal _ _ same
  have safe : column.val + (1#usize).val ≤ Usize.max := by
    change column.val + 1 ≤ Usize.max
    exact (Nat.succ_le_of_lt affineRoom).trans shape.affine.length_ineq
  obtain ⟨length, added, value⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := column) (y := 1#usize) safe)
  change length.val = column.val + 1 at value
  refine ⟨length, value, ?_⟩
  rw [modelExact]
  unfold nextColumn at yielded
  simp only [columnBody, multiple_loop0.body, yielded, bind_ok]
  dsimp! only
  simp only [vectorCopy, fill_zero, bind_ok, witnessUpdate,
    show (zeroWords state.witness).setAtNat column.val 1#u64 = initialWitness column state.witness from rfl, run]
  dsimp! only
  simp only [core.slice.index.Slice.index_mut, core.slice.index.Slice.index, cutAffine, cutWitness, bind_ok]
  dsimp! only
  simp only [copied, added, bind_ok]

def normalizedRows (degree row : Nat) (rows vector : Slice U64) (inverse : U64) : Slice U64 :=
  let begin := row * degree + row
  rows.setSlice! begin
    (MutableZip.mapFrom (region rows begin ((row + 1) * degree))
      (tail vector row) (scaleWord inverse) 0).val

def normalizedWitnesses (width row column : Nat) (witnesses witness : Slice U64) (inverse : U64) : Slice U64 :=
  let begin := row * width
  witnesses.setSlice! begin
    (MutableZip.mapFrom (region witnesses begin (begin + column + 1))
      (prefixSlice witness (column + 1)) (scaleWord inverse) 0).val

def columnSquareReady {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (shape : ColumnShape) (state : ColumnState) (column : Usize) : Prop :=
  column ≠ 0#usize → column ≠ shape.degree →
    ∀ vector : Slice U64, vector.length = shape.degree.val →
      ∃ size squared raw,
        square RootSetup.gf64Dictionary kernels state.residue shape.polynomial shape.table vector state.raw =
          .ok (size, squared, raw) ∧ squared.length = shape.degree.val ∧ raw.length = state.raw.length

def advancedResidue {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (shape : ColumnShape) (state : ColumnState)
    (column : Usize) (vector : Slice U64) : Result (Slice U64 × Slice U64 × Slice RawProduct) :=
  if column = 0#usize then .ok ((zeroWords state.residue).setAtNat 1 1#u64, vector, state.raw)
  else if column = shape.degree then .ok (state.residue, vector, state.raw)
  else do
    let (_, squared, raw) ← square RootSetup.gf64Dictionary kernels state.residue shape.polynomial shape.table vector state.raw
    .ok (squared, squared, raw)

private theorem shared_suffix_normal (words : Slice U64) (start : Usize) (fits : start.val ≤ words.length) :
    core.slice.index.SliceIndexRangeFromUsizeSlice.index ⟨start⟩ words = .ok (tail words start.val) := by
  obtain ⟨suffix, normal, suffixValue, _⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec ⟨start⟩ words fits)
  rw [normal]
  exact congrArg Result.ok (Slice.ext _ _ (by simpa only [tail, Slice.from_val] using suffixValue))

private theorem pivot_inverse {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (law : BmTerminal.NativeInverse kernels) (word : U64) (nonzero : word ≠ 0#u64) :
    (if word = 1#u64 then Result.ok 1#u64 else do
      let option ← kernels.ArithmeticInst.inverse word
      core.option.Option.expect option (toStr "nonzero affine pivot")) =
      .ok (DenseDivision.divisorInverse word) := by
  by_cases one : word = 1#u64
  · simp only [one, ite_true, DenseDivision.divisorInverse]
  · rw [ite_eq_right one, law, InverseUsing.inverse_refines]
    simp only [Inverse.expectedFieldInverse, nonzero, ite_false, bind_ok, core.option.Option.expect,
      DenseDivision.divisorInverse, one, DirectTwo.inverseWord]
    rfl

/-- The original column continuation normalizes both selected row windows
and advances its residue exactly, including the first and last columns. -/
theorem pivot_column_refines {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (scaleLaw : TimesXMod.ExactScaleXor kernels) (mulLaw : DenseDivRem.MulWordLaw kernels)
    (inverseLaw : BmTerminal.NativeInverse kernels)
    (restores : ColumnRestores) (shape : ColumnShape) (iter next : ColumnIter) (state : ColumnState)
    (column : Usize) (ready : columnReady shape column state) (minimum : 2 ≤ shape.degree.val)
    (squareReady : columnSquareReady square kernels shape state column)
    (yielded : nextColumn iter = .ok (some column, next))
    (found : ∃ row, (pivotSearch shape.degree.val column.val state.rows state.witnesses
      shape.degree.val 0 state.residue (initialWitness column state.witness)).2.2 = some row) :
    ∃ (vector witness : Slice U64) (row : Usize) (advanced : ColumnState),
      pivotSearch shape.degree.val column.val state.rows state.witnesses
        shape.degree.val 0 state.residue (initialWitness column state.witness) =
        (vector, witness, some row.val) ∧
      advanced.rows = normalizedRows shape.degree.val row.val state.rows vector
        (DenseDivision.divisorInverse vector[row.val]!) ∧
      advanced.witnesses = normalizedWitnesses shape.width.val row.val column.val state.witnesses witness
        (DenseDivision.divisorInverse vector[row.val]!) ∧
      advanced.witness = witness ∧
      advancedResidue square kernels shape state column vector =
        .ok (advanced.residue, advanced.vector, advanced.raw) ∧
      advanced.residue.length = shape.degree.val ∧ advanced.vector.length = shape.degree.val ∧
      advanced.witness.length = shape.width.val ∧ advanced.raw.length = state.raw.length ∧
      columnBody square kernels restores shape iter state = .ok (.cont (columnContinue next advanced)) := by
  obtain ⟨layout, residueWidth, _⟩ := ready
  have witnessRoom : column.val < state.witness.length := by
    rw [layout.witnessWidth, layout.widthValue]
    exact Nat.lt_succ_of_le layout.columnRoom
  have initialLength : (initialWitness column state.witness).length = shape.width.val := by
    simp only [initialWitness, Slice.setAtNat_length, zero_length, layout.witnessWidth]
  have initialLayout : PivotLayout shape.degree shape.width column state.rows state.witnesses
      state.residue (initialWitness column state.witness) :=
    ⟨layout.widthValue, layout.columnRoom, layout.rowsRoom, layout.witnessesRoom, residueWidth, initialLength⟩
  obtain ⟨vector, witness, pivot, run, model, finalLayout, pivotMeaning⟩ :=
    pivot_search_refines kernels scaleLaw shape.degree shape.width column state.rows state.witnesses
      state.residue (initialWitness column state.witness) ⟨0#usize, shape.degree⟩ initialLayout rfl
  have modelExact : pivotSearch shape.degree.val column.val state.rows state.witnesses
      shape.degree.val 0 state.residue (initialWitness column state.witness) =
      (vector, witness, pivot.map UScalar.val) := by
    simpa only [show (0#usize).val = 0 by decide, Nat.sub_zero] using model
  obtain ⟨index, positivePivot⟩ := found
  rw [modelExact] at positivePivot
  cases pivot with
  | none => contradiction
  | some row =>
    obtain ⟨_, rowActive, _, nonzero⟩ := pivotMeaning row rfl
    let inverse := DenseDivision.divisorInverse vector[row.val]!
    let rows := normalizedRows shape.degree.val row.val state.rows vector inverse
    let witnesses := normalizedWitnesses shape.width.val row.val column.val state.witnesses witness inverse
    have witnessLength := finalLayout.witnessWidth
    have vectorLength := finalLayout.vectorWidth
    have inv := pivot_inverse kernels inverseLaw vector[row.val]! nonzero
    have vectorCopy := ClosedLeaf.copy_normal state.vector state.residue (layout.vectorWidth.trans residueWidth.symm)
    have witnessUpdate := Reconstruction.update_normal (zeroWords state.witness) column 1#u64 (by
      rw [zero_length]
      exact witnessRoom)
    have searchedRead := read_normal vector row (by rw [vectorLength]; exact rowActive)
    obtain ⟨rowStarts, rowEnds, rowSpan⟩ := row_window rowActive
    obtain ⟨witnessEnds, _⟩ := witness_window rowActive layout.columnRoom
    have rowArena := layout.rowsRoom
    have witnessArena := layout.witnessesRoom
    rw [layout.widthValue] at witnessArena
    have rowsMax : state.rows.length ≤ Usize.max := state.rows.length_ineq
    have witnessesMax : state.witnesses.length ≤ Usize.max := state.witnesses.length_ineq
    have vectorMax : vector.length ≤ Usize.max := vector.length_ineq
    obtain ⟨rowBase, rowBaseNormal, rowBaseValue⟩ := mul_normal row shape.degree (by omega)
    obtain ⟨rowStart, rowStartNormal, rowStartValue⟩ := add_normal rowBase row (by rw [rowBaseValue]; omega)
    have rowStartEq : rowStart.val = row.val * shape.degree.val + row.val := by rw [rowStartValue, rowBaseValue]
    obtain ⟨afterRow, afterNormal, afterValue⟩ := add_normal row 1#usize (by
      change row.val + 1 ≤ Usize.max
      omega)
    change afterRow.val = row.val + 1 at afterValue
    obtain ⟨rowStop, rowStopNormal, rowStopValue⟩ := mul_normal afterRow shape.degree (by rw [afterValue]; omega)
    have rowStopEq : rowStop.val = (row.val + 1) * shape.degree.val := by rw [rowStopValue, afterValue]
    obtain ⟨wBase, wBaseNormal, wBaseValue⟩ := mul_normal row shape.width (by rw [layout.widthValue]; omega)
    have wBaseEq : wBase.val = row.val * (shape.degree.val + 1) := by rw [wBaseValue, layout.widthValue]
    obtain ⟨wLast, wLastNormal, wLastValue⟩ := add_normal wBase column (by rw [wBaseEq]; omega)
    have wLastEq : wLast.val = row.val * (shape.degree.val + 1) + column.val := by rw [wLastValue, wBaseEq]
    obtain ⟨wStop, wStopNormal, wStopValue⟩ := add_normal wLast 1#usize (by
      rw [wLastEq]
      change row.val * (shape.degree.val + 1) + column.val + 1 ≤ Usize.max
      omega)
    have wStopEq : wStop.val = row.val * (shape.degree.val + 1) + column.val + 1 := by
      change wStop.val = wLast.val + 1 at wStopValue
      rw [wStopValue, wLastEq]
    have rowCut := ClosedLeaf.mutable_region_normal state.rows rowStart rowStop
      (by rw [rowStartEq, rowStopEq]; omega) (by rw [rowStopEq]; omega)
    have vectorCut := shared_suffix_normal vector row (by omega)
    have witnessCut := ClosedLeaf.mutable_region_normal state.witnesses wBase wStop
      (by rw [wBaseEq, wStopEq]; omega) (by rw [wStopEq]; omega)
    have witnessInput := ClosedLeaf.inclusive_prefix_normal witness column
      (by rw [witnessLength, layout.widthValue]; exact Nat.lt_succ_of_le layout.columnRoom)
    let rowWindow := region state.rows rowStart.val rowStop.val
    let witnessWindow := region state.witnesses wBase.val wStop.val
    let vectorTail := tail vector row.val
    let witnessPrefix := prefixSlice witness (column.val + 1)
    have rowSame : rowWindow.length = vectorTail.length := by
      rw [show rowWindow.length = rowStop.val - rowStart.val from ClosedLeaf.region_length _ _ _ (by omega),
        rowStopEq, rowStartEq, rowSpan, show vectorTail.length = vector.length - row.val from tail_length _ _, vectorLength]
    have witnessSame : witnessWindow.length = witnessPrefix.length := by
      rw [show witnessWindow.length = wStop.val - wBase.val from ClosedLeaf.region_length _ _ _ (by omega),
        show witnessPrefix.length = min (column.val + 1) witness.length from prefix_length _ _,
        Nat.min_eq_left (by rw [witnessLength, layout.widthValue]; exact Nat.succ_le_succ layout.columnRoom),
        wStopEq, wBaseEq]
      omega
    obtain ⟨rowBack, normalizedRow, rowApply⟩ := row_normalization_refines kernels mulLaw inverse
      rowWindow vectorTail rowSame 0 (Nat.zero_le _) id
    obtain ⟨witnessBack, normalizedWitness, witnessApply⟩ := witness_normalization_refines kernels mulLaw inverse
      witnessWindow witnessPrefix witnessSame 0 (Nat.zero_le _) id
    have rowRun : multiple_loop0_loop1 RootSetup.gf64Dictionary kernels
        (MutableZip.stateAt rowWindow vectorTail 0) (fun state => state) inverse =
        .ok (MutableZip.stateAt rowWindow vectorTail rowWindow.length, rowBack) := normalizedRow
    have witnessRun : multiple_loop0_loop2 RootSetup.gf64Dictionary kernels
        (MutableZip.stateAt witnessWindow witnessPrefix 0) (fun state => state) inverse =
        .ok (MutableZip.stateAt witnessWindow witnessPrefix witnessWindow.length, witnessBack) := normalizedWitness
    have exactRows : state.rows.setSlice! rowStart.val
        ((rowBack (MutableZip.stateAt rowWindow vectorTail rowWindow.length)).fst.slice.val) = rows := by
      rw [rowApply]
      simp only [id_eq, MutableZip.stateAt, rows, normalizedRows, rowWindow, vectorTail, rowStartEq, rowStopEq]
    have exactWitnesses : state.witnesses.setSlice! wBase.val
        ((witnessBack (MutableZip.stateAt witnessWindow witnessPrefix witnessWindow.length)).fst.slice.val) = witnesses := by
      rw [witnessApply]
      simp only [id_eq, MutableZip.stateAt, witnesses, normalizedWitnesses, witnessWindow, witnessPrefix,
        wBaseEq, wStopEq, layout.widthValue]
    let continuation : Result (ControlFlow ColumnContinue ColumnDone) := do
      if column = 0#usize then
        .ok (.cont (next, state.raw, rows, witnesses, (zeroWords state.residue).setAtNat 1 1#u64, vector, witness))
      else if column != shape.degree then do
        let (_, squared, raw) ← square RootSetup.gf64Dictionary kernels state.residue shape.polynomial shape.table vector state.raw
        let residue ← core.slice.Slice.copy_from_slice core.marker.CopyU64 state.residue squared
        .ok (.cont (next, raw, rows, witnesses, residue, squared, witness))
      else .ok (.cont (next, state.raw, rows, witnesses, state.residue, vector, witness))
    have original : columnBody square kernels restores shape iter state = continuation := by
      unfold nextColumn at yielded
      simp only [columnBody, multiple_loop0.body, yielded, bind_ok]
      dsimp! only
      simp only [vectorCopy, fill_zero, bind_ok, witnessUpdate,
        show (zeroWords state.witness).setAtNat column.val 1#u64 = initialWitness column state.witness from rfl, run]
      dsimp! only
      simp only [searchedRead, bind_ok, inv, show DenseDivision.divisorInverse vector[row.val]! = inverse from rfl,
        rowBaseNormal, rowStartNormal, afterNormal, rowStopNormal,
        Slice.index_mut_SliceIndexRangeUsizeSliceInst, rowCut, core.slice.Slice.iter_mut,
        Slice.index_SliceIndexRangeFromUsizeSliceInst, vectorCut]
      dsimp! only
      simp only [show region state.rows rowStart.val rowStop.val = rowWindow from rfl,
        show tail vector row.val = vectorTail from rfl, bind_ok,
        wBaseNormal, wLastNormal, wStopNormal, witnessCut,
        core.slice.index.Slice.index, witnessInput, MutableZip.construct]
      dsimp! only
      simp only [show region state.witnesses wBase.val wStop.val = witnessWindow from rfl,
        show prefixSlice witness (column.val + 1) = witnessPrefix from rfl, witnessRun, bind_ok]
      rw [rowRun, bind_ok]
      dsimp! only
      by_cases first : column = 0#usize
      · have update := Reconstruction.update_normal (zeroWords state.residue) 1#usize 1#u64 (by
          rw [zero_length, residueWidth]; exact minimum)
        simp only [first, ite_true, bind_ok, update, exactRows, exactWitnesses, continuation]
        rfl
      · simp only [ite_eq_right first, continuation]
        by_cases last : column = shape.degree
        · simp only [last, bne_self_eq_false, Bool.false_eq_true, ite_false, exactRows, exactWitnesses]
        · have notLast : (column != shape.degree) = true := by simp [last]
          simp only [notLast, ite_true, exactRows, exactWitnesses]
    by_cases first : column = 0#usize
    · let advanced : ColumnState := ⟨state.raw, rows, witnesses,
          (zeroWords state.residue).setAtNat 1 1#u64, vector, witness⟩
      refine ⟨vector, witness, row, advanced, ?_, rfl, rfl, rfl, ?_, ?_, vectorLength, witnessLength, rfl, ?_⟩
      · simpa only [Option.map_some] using modelExact
      · simp only [advancedResidue, first, ite_true, advanced]
      · simp only [advanced, Slice.setAtNat_length, zero_length, residueWidth]
      · simp only [original, continuation, first, ite_true, columnContinue, advanced]
    · by_cases last : column = shape.degree
      · let advanced : ColumnState := ⟨state.raw, rows, witnesses, state.residue, vector, witness⟩
        refine ⟨vector, witness, row, advanced, ?_, rfl, rfl, rfl, ?_, residueWidth, vectorLength, witnessLength, rfl, ?_⟩
        · simpa only [Option.map_some] using modelExact
        · rw [advancedResidue, ite_eq_right first, ite_eq_left last]
        · simp only [original, continuation, ite_eq_right first, last, bne_self_eq_false, Bool.false_eq_true, ite_false,
            columnContinue, advanced]
      · obtain ⟨size, squared, raw, squaredNormal, squaredWidth, rawWidth⟩ :=
          squareReady first last vector vectorLength
        have copied := ClosedLeaf.copy_normal state.residue squared (residueWidth.trans squaredWidth.symm)
        let advanced : ColumnState := ⟨raw, rows, witnesses, squared, squared, witness⟩
        refine ⟨vector, witness, row, advanced, ?_, rfl, rfl, rfl, ?_, squaredWidth, squaredWidth, witnessLength, rawWidth, ?_⟩
        · simpa only [Option.map_some] using modelExact
        · simp only [advancedResidue, ite_eq_right first, ite_eq_right last, squaredNormal, bind_ok, advanced]
          rfl
        · have notLast : (column != shape.degree) = true := by simp [last]
          simp only [original, continuation, ite_eq_right first, notLast, ite_true, squaredNormal, bind_ok]
          dsimp! only
          simp only [copied, bind_ok, columnContinue, advanced]

end BulksketchBridge.AffineMultiple
