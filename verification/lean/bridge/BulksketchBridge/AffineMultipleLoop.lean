import BulksketchBridge.AffineMultipleColumn

namespace BulksketchBridge.AffineMultiple

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.backend.contract bulksketch.decode.affine
open DenseCoefficient RebuiltLfsr

set_option maxRecDepth 4096
set_option maxHeartbeats 1700000

def searchedColumn (shape : ColumnShape) (state : ColumnState) (column : Usize) : PivotResult :=
  pivotSearch shape.degree.val column.val state.rows state.witnesses shape.degree.val 0
    state.residue (initialWitness column state.witness)

def dependentOutput (restores : ColumnRestores) (shape : ColumnShape) (state : ColumnState)
    (column length : Usize) : ColumnDone :=
  let (vector, witness, _) := searchedColumn shape state column
  (length, restores.factors (state.rows, restores.witnesses state.witnesses),
    restorePrefix shape.affine (prefixSlice witness (column.val + 1)),
    restores.work (state.residue, restores.vector (vector, restores.witness witness)), state.raw)

def ColumnStored {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (shape : ColumnShape)
    (state : ColumnState) (column : Usize) (advanced : ColumnState) : Prop :=
  ∃ (vector witness : Slice U64) (row : Usize),
    searchedColumn shape state column = (vector, witness, some row.val) ∧
    advanced.rows = normalizedRows shape.degree.val row.val state.rows vector
      (DenseDivision.divisorInverse vector[row.val]!) ∧
    advanced.witnesses = normalizedWitnesses shape.width.val row.val column.val state.witnesses witness
      (DenseDivision.divisorInverse vector[row.val]!) ∧
    advanced.witness = witness ∧
    advancedResidue square kernels shape state column vector =
      .ok (advanced.residue, advanced.vector, advanced.raw)

private theorem stored_unique {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (shape : ColumnShape) (state : ColumnState)
    (column : Usize) (left right : ColumnState)
    (a : ColumnStored square kernels shape state column left)
    (b : ColumnStored square kernels shape state column right) : left = right := by
  obtain ⟨leftVector, leftWitness, leftRow, leftSearch, leftRows, leftWitnesses, leftWitnessEq, leftResidue⟩ := a
  obtain ⟨rightVector, rightWitness, rightRow, rightSearch, rightRows, rightWitnesses, rightWitnessEq, rightResidue⟩ := b
  have same := leftSearch.symm.trans rightSearch
  obtain ⟨vectorEq, witnessEq, rowEq⟩ := by simpa only [Prod.mk.injEq, Option.some.injEq] using same
  rw [← vectorEq] at rightRows rightWitnesses rightResidue
  rw [← witnessEq] at rightWitnesses rightWitnessEq
  have sameRow : leftRow = rightRow := UScalar.eq_of_val_eq rowEq
  subst rightRow
  have output := Result.ok_injective (leftResidue.symm.trans rightResidue)
  obtain ⟨residueEq, vectorEq, rawEq⟩ := by simpa only [Prod.mk.injEq] using output
  have rowsEq := leftRows.trans rightRows.symm
  have witnessesEq := leftWitnesses.trans rightWitnesses.symm
  have witnessEq := leftWitnessEq.trans rightWitnessEq.symm
  cases left
  cases right
  simp_all

/-- The independent finite column recurrence. Each successful transition uses
only the checked input bounds and the separately scoped square contract. -/
inductive ColumnTrace {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (restores : ColumnRestores) (shape : ColumnShape) :
    ColumnIter → ColumnState → Result ColumnDone → Prop where
  | exhausted {iter next state} :
      nextColumn iter = .ok (none, next) →
      ColumnTrace square kernels restores shape iter state (.fail .panic)
  | dependent {iter next state column length} :
      nextColumn iter = .ok (some column, next) →
      columnReady shape column state →
      (searchedColumn shape state column).2.2 = none →
      length.val = column.val + 1 →
      ColumnTrace square kernels restores shape iter state
        (.ok (dependentOutput restores shape state column length))
  | pivot {iter next state column advanced result} :
      nextColumn iter = .ok (some column, next) →
      columnReady shape column state →
      2 ≤ shape.degree.val →
      columnSquareReady square kernels shape state column →
      ColumnStored square kernels shape state column advanced →
      ColumnTrace square kernels restores shape next advanced result →
      ColumnTrace square kernels restores shape iter state result

def columnLoop {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (restores : ColumnRestores) (shape : ColumnShape)
    (iter : ColumnIter) (state : ColumnState) : Result ColumnDone :=
  multiple_loop0 square RootSetup.gf64Dictionary kernels restores.factors restores.witnesses
    restores.work restores.vector restores.witness iter shape.polynomial shape.table shape.affine
    state.raw shape.degree shape.width state.rows state.witnesses state.residue state.vector state.witness

theorem column_loop_refines_trace {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (scaleLaw : TimesXMod.ExactScaleXor kernels) (mulLaw : DenseDivRem.MulWordLaw kernels)
    (inverseLaw : BmTerminal.NativeInverse kernels)
    (restores : ColumnRestores) (shape : ColumnShape) (iter : ColumnIter) (state : ColumnState)
    (result : Result ColumnDone) (trace : ColumnTrace square kernels restores shape iter state result) :
    columnLoop square kernels restores shape iter state = result := by
  induction trace with
  | @exhausted iter next state yielded =>
    have step := exhausted_columns square kernels restores shape iter next state yielded
    unfold columnBody at step
    unfold columnLoop multiple_loop0 loop
    dsimp only
    rw [step, bind_fail]
  | @dependent iter next state column length yielded ready dependent lengthValue =>
    obtain ⟨actualLength, actualValue, step⟩ :=
      dependent_column_refines square kernels scaleLaw restores shape iter next state column ready yielded dependent
    have same : actualLength = length := UScalar.eq_of_val_eq (actualValue.trans lengthValue.symm)
    subst actualLength
    change columnBody square kernels restores shape iter state =
      .ok (.done (dependentOutput restores shape state column length)) at step
    unfold columnBody at step
    unfold columnLoop multiple_loop0 loop
    dsimp only
    rw [step, bind_ok]
  | @pivot iter next state column advanced result yielded ready minimum squareReady stored tail rest =>
    have found : ∃ row, (searchedColumn shape state column).2.2 = some row := by
      obtain ⟨vector, witness, row, search, _⟩ := stored
      exact ⟨row.val, by rw [search]⟩
    obtain ⟨vector, witness, row, actual, search, rows, witnesses, witnessEq, residue, _, _, _, _, step⟩ :=
      pivot_column_refines square kernels scaleLaw mulLaw inverseLaw restores shape iter next state
        column ready minimum squareReady yielded found
    have same := stored_unique square kernels shape state column actual advanced
      ⟨vector, witness, row, search, rows, witnesses, witnessEq, residue⟩ stored
    subst actual
    unfold columnBody at step
    unfold columnLoop multiple_loop0 loop
    dsimp only
    simpa only [step, bind_ok, columnContinue, columnLoop, multiple_loop0] using rest

def columnsLeft (iter : ColumnIter) : Nat :=
  if iter.exhausted then 0 else iter.«end».val + 1 - iter.start.val

private theorem checked_next_column (iter : ColumnIter) :
    ∃ (option : Option Usize) (next : ColumnIter),
      nextColumn iter = .ok (option, next) ∧
      ∀ column, option = some column →
        column.val ≤ iter.«end».val ∧ next.«end» = iter.«end» ∧ columnsLeft next < columnsLeft iter := by
  obtain ⟨⟨option, next⟩, normal, meaning⟩ := RawMulTable.normal_of_spec _ _
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec iter)
  dsimp only [WP.uncurry'] at meaning
  refine ⟨option, next, normal, ?_⟩
  intro column found
  by_cases empty : iter.exhausted ∨ iter.«end».val < iter.start.val
  · rw [ite_eq_left empty] at meaning
    rw [meaning.1] at found
    contradiction
  · rw [ite_eq_right empty] at meaning
    have active : iter.start.val ≤ iter.«end».val := by
      exact Nat.le_of_not_gt (fun greater => empty (.inr greater))
    have unexhausted : iter.exhausted = false := Bool.eq_false_iff.mpr (fun yes => empty (.inl yes))
    by_cases before : iter.start.val < iter.«end».val
    · rw [ite_eq_left before] at meaning
      obtain ⟨read, advanced, ending, unexhaustedNext⟩ := meaning
      have columnEq := Option.some.inj (found.symm.trans read)
      subst column
      refine ⟨active, ending, ?_⟩
      simp only [columnsLeft, unexhausted, unexhaustedNext, Bool.false_eq_true, ite_false, advanced, ending]
      omega
    · rw [ite_eq_right before] at meaning
      obtain ⟨read, _, ending, exhaustedNext⟩ := meaning
      have columnEq := Option.some.inj (found.symm.trans read)
      subst column
      refine ⟨active, ending, ?_⟩
      simp only [columnsLeft, unexhausted, exhaustedNext, Bool.false_eq_true, ite_false, ite_true]
      omega

/-- The admitted affine arenas keep their dimensions throughout the column
loop. The raw bound permits the original modular-square implementation. -/
def ColumnArena (shape : ColumnShape) (state : ColumnState) : Prop :=
  PivotLayout shape.degree shape.width 0#usize state.rows state.witnesses state.vector state.witness ∧
  state.residue.length = shape.degree.val ∧
  shape.degree.val + 1 ≤ shape.affine.length ∧
  2 * shape.degree.val < state.raw.length

theorem column_trace_exists {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (scaleLaw : TimesXMod.ExactScaleXor kernels) (mulLaw : DenseDivRem.MulWordLaw kernels)
    (inverseLaw : BmTerminal.NativeInverse kernels)
    (restores : ColumnRestores) (shape : ColumnShape)
    (minimum : 2 ≤ shape.degree.val)
    (squareLaw : ∀ (state : ColumnState) (column : Usize), ColumnArena shape state →
      column.val ≤ shape.degree.val → columnSquareReady square kernels shape state column)
    (iter : ColumnIter) (state : ColumnState) (ending : iter.«end» = shape.degree) (arena : ColumnArena shape state) :
    ∃ result, ColumnTrace square kernels restores shape iter state result := by
  suffices ∀ (fuel : Nat) (iter : ColumnIter) (state : ColumnState),
      columnsLeft iter = fuel → iter.«end» = shape.degree → ColumnArena shape state →
      ∃ result, ColumnTrace square kernels restores shape iter state result from this _ iter state rfl ending arena
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro iter state count ending arena
    obtain ⟨option, next, checked, advances⟩ := checked_next_column iter
    cases option with
    | none => exact ⟨.fail .panic, .exhausted checked⟩
    | some column =>
      obtain ⟨columnEnd, nextEnd, fewer⟩ := advances column rfl
      have columnRoom : column.val ≤ shape.degree.val := by rwa [ending] at columnEnd
      have squareReady := squareLaw state column arena columnRoom
      obtain ⟨layout, residueWidth, affineRoom, rawRoom⟩ := arena
      have ready : columnReady shape column state :=
        ⟨⟨layout.widthValue, columnRoom, layout.rowsRoom, layout.witnessesRoom, layout.vectorWidth, layout.witnessWidth⟩,
          residueWidth, by omega⟩
      cases pivot : (searchedColumn shape state column).2.2 with
      | none =>
        obtain ⟨length, value, _⟩ := dependent_column_refines square kernels scaleLaw restores shape iter next
          state column ready checked pivot
        exact ⟨.ok (dependentOutput restores shape state column length), .dependent checked ready pivot value⟩
      | some row =>
        obtain ⟨vector, witness, actualRow, advanced, search, writtenRows, writtenWitnesses, witnessEq, residue,
            nextResidueWidth, nextVectorWidth, nextWitnessWidth, rawWidth, _⟩ :=
          pivot_column_refines square kernels scaleLaw mulLaw inverseLaw restores shape iter next state
            column ready minimum squareReady checked ⟨row, pivot⟩
        have rowLength : advanced.rows.length = state.rows.length := by
          rw [writtenRows, normalizedRows, Slice.setSlice!_length]
        have witnessesLength : advanced.witnesses.length = state.witnesses.length := by
          rw [writtenWitnesses, normalizedWitnesses, Slice.setSlice!_length]
        have nextArena : ColumnArena shape advanced :=
          ⟨⟨layout.widthValue, layout.columnRoom, by rw [rowLength]; exact layout.rowsRoom,
            by rw [witnessesLength]; exact layout.witnessesRoom, nextVectorWidth, nextWitnessWidth⟩,
            nextResidueWidth, affineRoom, by rwa [rawWidth]⟩
        obtain ⟨result, tail⟩ := ih (columnsLeft next) (by omega) next advanced rfl (nextEnd.trans ending) nextArena
        refine ⟨result, .pivot checked ready minimum squareReady ?_ tail⟩
        exact ⟨vector, witness, actualRow, search, writtenRows, writtenWitnesses, witnessEq, residue⟩

end BulksketchBridge.AffineMultiple
