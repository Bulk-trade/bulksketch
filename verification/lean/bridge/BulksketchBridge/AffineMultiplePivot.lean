import Arithmetic.AffineMultipleGenerated
import BulksketchBridge.AffineMultipleBounds
import BulksketchBridge.PortableZipMap
import BulksketchBridge.RebuiltLfsr
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.BmEntry
import BulksketchBridge.TimesXModSpec

namespace BulksketchBridge.AffineMultiple

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.backend.contract bulksketch.decode.affine
open DenseCoefficient RebuiltLfsr BmEntry
open ClosedLeaf (region)
open Algebra.Gf64 (multiplyWord)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev PivotResult := Slice U64 × Slice U64 × Option Nat

structure PivotLayout (degree width column : Usize) (rows witnesses vector witness : Slice U64) : Prop where
  widthValue : width.val = degree.val + 1
  columnRoom : column.val ≤ degree.val
  rowsRoom : degree.val * degree.val ≤ rows.length
  witnessesRoom : degree.val * width.val ≤ witnesses.length
  vectorWidth : vector.length = degree.val
  witnessWidth : witness.length = width.val

def scaleWindow (destination source : Slice U64) (scale : U64) : Slice U64 :=
  MutableZip.mapFrom destination source
    (fun old value => old ^^^ (⟨multiplyWord scale.bv value.bv⟩ : U64)) 0

def eliminateRow (degree column : Nat) (rows witnesses : Slice U64) (row : Nat)
    (vector witness : Slice U64) : Slice U64 × Slice U64 :=
  let scale := vector[row]!
  let rowStart := row * degree + row
  let witnessStart := row * (degree + 1)
  (vector.setSlice! row
      (scaleWindow (tail vector row) (region rows rowStart ((row + 1) * degree)) scale).val,
    restorePrefix witness
      (scaleWindow (prefixSlice witness (column + 1))
        (region witnesses witnessStart (witnessStart + column + 1)) scale))

/-- A zero vector coefficient leaves both windows unchanged. A nonzero
coefficient at an unused diagonal selects the pivot. An occupied diagonal
updates exactly the trailing vector and current witness prefix. -/
def pivotRow (degree column : Nat) (rows witnesses : Slice U64) (row : Nat)
    (vector witness : Slice U64) : Option (Slice U64 × Slice U64) :=
  if vector[row]! = 0#u64 then some (vector, witness)
  else if rows[row * degree + row]! = 0#u64 then none
  else some (eliminateRow degree column rows witnesses row vector witness)

def pivotSearch (degree column : Nat) (rows witnesses : Slice U64) :
    Nat → Nat → Slice U64 → Slice U64 → PivotResult
  | 0, _, vector, witness => (vector, witness, none)
  | fuel + 1, row, vector, witness =>
    match pivotRow degree column rows witnesses row vector witness with
    | none => (vector, witness, some row)
    | some (nextVector, nextWitness) =>
      pivotSearch degree column rows witnesses fuel (row + 1) nextVector nextWitness

/-- The concrete checked scale-XOR callback writes the independent word map. -/
theorem scale_window_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (law : TimesXMod.ExactScaleXor kernels) (destination source : Slice U64) (scale : U64)
    (same : destination.length = source.length) :
    kernels.ArithmeticInst.scale_xor destination source scale =
      .ok (scaleWindow destination source scale) := by
  obtain ⟨output, normal, length, word⟩ := law destination source scale same
  have exact : output = scaleWindow destination source scale := by
    apply Slice.ext_getElem (by simpa [scaleWindow] using length)
    intro i left right
    rw [Slice.Inhabited_getElem_eq_getElem! _ _ left,
      Slice.Inhabited_getElem_eq_getElem! _ _ right]
    have inside : i < destination.length := by omega
    rw [word i inside]
    simp only [scaleWindow, MutableZip.mapFrom_word _ _ _ _ _ inside, Nat.zero_le, ite_true]
  rw [normal, exact]

theorem read_normal (words : Slice U64) (index : Usize)
    (bounded : index.val < words.length) :
    Slice.index_usize words index = .ok words[index.val]! := by
  obtain ⟨value, normal, exact⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bounded)
  rw [normal, exact]
  exact congrArg Result.ok (Slice.Inhabited_getElem_eq_getElem! words index.val bounded)

private theorem suffix_normal (words : Slice U64) (start : Usize) (fits : start.val ≤ words.length) :
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut ⟨start⟩ words =
      .ok (tail words start.val, fun replacement => words.setSlice! start.val replacement.val) := by
  obtain ⟨⟨suffix, back⟩, normal, suffixValue, _, backValue⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.step_spec ⟨start⟩ words fits)
  have suffixEq : suffix = tail words start.val := by
    apply Slice.ext
    simpa only [tail, Slice.from_val] using suffixValue
  have backEq : back = (fun replacement => words.setSlice! start.val replacement.val) := by
    funext replacement
    apply Slice.ext
    simpa only [Slice.setSlice!_val] using backValue replacement
  rw [normal, suffixEq, backEq]

theorem add_normal (left right : Usize) (fits : left.val + right.val ≤ Usize.max) :
    ∃ sum : Usize, (left + right : Result Usize) = .ok sum ∧ sum.val = left.val + right.val :=
  RawMulTable.normal_of_spec _ _ (Usize.add_spec (x := left) (y := right) fits)

theorem mul_normal (left right : Usize) (fits : left.val * right.val ≤ Usize.max) :
    ∃ product : Usize, (left * right : Result Usize) = .ok product ∧ product.val = left.val * right.val :=
  RawMulTable.normal_of_spec _ _ (Usize.mul_spec (x := left) (y := right) fits)

private theorem continue_layout {degree width column : Usize} {rows witnesses vector witness : Slice U64}
    (layout : PivotLayout degree width column rows witnesses vector witness) (row : Nat)
    (updated : Slice U64 × Slice U64)
    (next : pivotRow degree.val column.val rows witnesses row vector witness = some updated) :
    PivotLayout degree width column rows witnesses updated.1 updated.2 := by
  rcases layout with ⟨widthValue, columnRoom, rowsRoom, witnessesRoom, vectorWidth, witnessWidth⟩
  have widths : updated.1.length = degree.val ∧ updated.2.length = width.val := by
    unfold pivotRow at next
    split at next
    · cases next
      exact ⟨vectorWidth, witnessWidth⟩
    · split at next
      · contradiction
      · cases next
        simp only [eliminateRow, Slice.setSlice!_length, restore_length, vectorWidth, witnessWidth, and_self]
  exact ⟨widthValue, columnRoom, rowsRoom, witnessesRoom, widths.1, widths.2⟩

private theorem pivot_row_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (law : TimesXMod.ExactScaleXor kernels)
    (degree width column : Usize) (rows witnesses vector witness : Slice U64)
    (iter next : core.ops.range.Range Usize)
    (layout : PivotLayout degree width column rows witnesses vector witness)
    (active : iter.start.val < degree.val)
    (yielded : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some iter.start, next)) :
    multiple_loop0_loop0.body RootSetup.gf64Dictionary kernels degree width rows witnesses column iter vector witness =
      .ok (match pivotRow degree.val column.val rows witnesses iter.start.val vector witness with
        | none => .done (vector, witness, some iter.start)
        | some (nextVector, nextWitness) => .cont (next, nextVector, nextWitness)) := by
  rcases layout with ⟨widthValue, columnRoom, rowsRoom, witnessesRoom, vectorWidth, witnessWidth⟩
  have vectorRead := read_normal vector iter.start (by rw [vectorWidth]; exact active)
  simp only [multiple_loop0_loop0.body, yielded, bind_ok]
  dsimp! only
  simp only [vectorRead, bind_ok, pivotRow]
  by_cases zero : vector[iter.start.val]! = 0#u64
  · simp only [zero, ite_true]
  · simp only [ite_eq_right zero]
    obtain ⟨diagonalFits, rowStopFits, rowLength⟩ := row_window active
    obtain ⟨witnessEndFits, _⟩ := witness_window active columnRoom
    rw [widthValue] at witnessesRoom
    have rowsMax : rows.length ≤ Usize.max := rows.length_ineq
    have witnessesMax : witnesses.length ≤ Usize.max := witnesses.length_ineq
    have witnessMax : witness.length ≤ Usize.max := witness.length_ineq
    have rowBaseFits : iter.start.val * degree.val ≤ Usize.max := by omega
    obtain ⟨base, baseNormal, baseValue⟩ := mul_normal iter.start degree rowBaseFits
    obtain ⟨diagonal, diagonalNormal, diagonalValue⟩ := add_normal base iter.start (by rw [baseValue]; omega)
    have diagonalEq : diagonal.val = iter.start.val * degree.val + iter.start.val := by rw [diagonalValue, baseValue]
    have diagonalRead := read_normal rows diagonal (by rw [diagonalEq]; omega)
    simp only [baseNormal, bind_ok, diagonalNormal, diagonalRead, diagonalEq]
    by_cases vacant : rows[iter.start.val * degree.val + iter.start.val]! = 0#u64
    · simp only [vacant, ite_true]
    · simp only [ite_eq_right vacant]
      obtain ⟨afterRow, afterNormal, afterValue⟩ := add_normal iter.start 1#usize (by
        change iter.start.val + 1 ≤ Usize.max
        have vectorMax : vector.length ≤ Usize.max := vector.length_ineq
        omega)
      change afterRow.val = iter.start.val + 1 at afterValue
      obtain ⟨rowStop, rowStopNormal, rowStopValue⟩ := mul_normal afterRow degree (by rw [afterValue]; omega)
      have stopEq : rowStop.val = (iter.start.val + 1) * degree.val := by rw [rowStopValue, afterValue]
      have vectorCut := suffix_normal vector iter.start (by omega)
      have rowCut := ClosedLeaf.shared_region_normal rows diagonal rowStop
        (by rw [diagonalEq, stopEq]; omega) (by rw [stopEq]; omega)
      have rowSize : (region rows (iter.start.val * degree.val + iter.start.val) ((iter.start.val + 1) * degree.val)).length =
          (tail vector iter.start.val).length := by
        rw [ClosedLeaf.region_length _ _ _ (by omega), rowLength, tail_length, vectorWidth]
      have vectorUpdate := scale_window_refines kernels law (tail vector iter.start.val)
        (region rows (iter.start.val * degree.val + iter.start.val) ((iter.start.val + 1) * degree.val))
        vector[iter.start.val]! rowSize.symm
      have witnessCut := RebuiltLfsr.inclusive_prefix witness column (by omega)
      obtain ⟨wBase, wBaseNormal, wBaseValue⟩ := mul_normal iter.start width (by rw [widthValue]; omega)
      have wBaseEq : wBase.val = iter.start.val * (degree.val + 1) := by rw [wBaseValue, widthValue]
      obtain ⟨wLast, wLastNormal, wLastValue⟩ := add_normal wBase column (by rw [wBaseEq]; omega)
      have wLastEq : wLast.val = iter.start.val * (degree.val + 1) + column.val := by rw [wLastValue, wBaseEq]
      obtain ⟨wStop, wStopNormal, wStopValue⟩ := add_normal wLast 1#usize (by
        rw [wLastEq]; change iter.start.val * (degree.val + 1) + column.val + 1 ≤ Usize.max; omega)
      have wStopEq : wStop.val = iter.start.val * (degree.val + 1) + column.val + 1 := by
        change wStop.val = wLast.val + 1 at wStopValue
        rw [wStopValue, wLastEq]
      have witnessRegion := ClosedLeaf.shared_region_normal witnesses wBase wStop
        (by rw [wBaseEq, wStopEq]; omega) (by rw [wStopEq]; omega)
      have updatedSame : (prefixSlice witness (column.val + 1)).length =
          (region witnesses (iter.start.val * (degree.val + 1)) (iter.start.val * (degree.val + 1) + column.val + 1)).length := by
        rw [prefix_length, Nat.min_eq_left (by omega), ClosedLeaf.region_length _ _ _ (by omega)]
        omega
      have witnessUpdate := scale_window_refines kernels law (prefixSlice witness (column.val + 1))
        (region witnesses (iter.start.val * (degree.val + 1)) (iter.start.val * (degree.val + 1) + column.val + 1))
        vector[iter.start.val]! updatedSame
      simp only [Slice.index_mut_SliceIndexRangeFromUsizeSliceInst, vectorCut, bind_ok]
      dsimp! only
      simp only [afterNormal, rowStopNormal, bind_ok,
        Slice.index_SliceIndexRangeUsizeSliceInst, rowCut, diagonalEq, stopEq, vectorUpdate,
        core.slice.index.Slice.index_mut, witnessCut]
      dsimp! only
      simp only [wBaseNormal, wLastNormal, wStopNormal, bind_ok,
        witnessRegion, wBaseEq, wStopEq, witnessUpdate]
      rfl

/-- The admitted original pivot search produces the exact row recurrence and
returns a nonzero coefficient at an unused row when a pivot is selected. -/
def ActualPivotSearch : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    TimesXMod.ExactScaleXor kernels → ∀ (degree width column : Usize)
      (rows witnesses vector witness : Slice U64) (iter : core.ops.range.Range Usize),
    PivotLayout degree width column rows witnesses vector witness → iter.«end» = degree →
    ∃ (finalVector finalWitness : Slice U64) (pivot : Option Usize),
      multiple_loop0_loop0 RootSetup.gf64Dictionary kernels iter degree width rows witnesses vector witness column =
        .ok (finalVector, finalWitness, pivot) ∧
      pivotSearch degree.val column.val rows witnesses (degree.val - iter.start.val) iter.start.val vector witness =
        (finalVector, finalWitness, pivot.map UScalar.val) ∧
      PivotLayout degree width column rows witnesses finalVector finalWitness ∧
      ∀ index, pivot = some index →
        iter.start.val ≤ index.val ∧ index.val < degree.val ∧
        rows[index.val * degree.val + index.val]! = 0#u64 ∧ finalVector[index.val]! ≠ 0#u64

theorem pivot_search_refines : ActualPivotSearch := by
  intro K kernels law degree width column rows witnesses vector witness iter layout stop
  suffices ∀ fuel (iter : core.ops.range.Range Usize) (vector witness : Slice U64),
      degree.val - iter.start.val = fuel → iter.«end» = degree →
      PivotLayout degree width column rows witnesses vector witness →
      ∃ (finalVector finalWitness : Slice U64) (pivot : Option Usize),
        multiple_loop0_loop0 RootSetup.gf64Dictionary kernels iter degree width rows witnesses vector witness column =
          .ok (finalVector, finalWitness, pivot) ∧
        pivotSearch degree.val column.val rows witnesses fuel iter.start.val vector witness =
          (finalVector, finalWitness, pivot.map UScalar.val) ∧
        PivotLayout degree width column rows witnesses finalVector finalWitness ∧
        ∀ index, pivot = some index →
          iter.start.val ≤ index.val ∧ index.val < degree.val ∧
          rows[index.val * degree.val + index.val]! = 0#u64 ∧ finalVector[index.val]! ≠ 0#u64
    from this _ iter vector witness rfl stop layout
  intro fuel
  induction fuel with
  | zero =>
    intro iter vector witness exhausted stop layout
    have inactive : iter.«end».val ≤ iter.start.val := by rw [stop]; omega
    obtain ⟨⟨result, next⟩, read, noneEq, _⟩ := RawMulTable.normal_of_spec _ _
      (core.iter.range.IteratorRange.next_Usize_none_spec iter inactive)
    rw [noneEq] at read
    refine ⟨vector, witness, none, ?_, rfl, layout, by intros; contradiction⟩
    unfold multiple_loop0_loop0 loop
    dsimp only
    simp only [multiple_loop0_loop0.body, read, bind_ok]
    dsimp! only
    simp only [bind_ok]
  | succ fuel ih =>
    intro iter vector witness count stop layout
    have active : iter.start.val < degree.val := by omega
    obtain ⟨⟨option, next⟩, read, someEq, advanced, nextStop⟩ := RawMulTable.normal_of_spec _ _
      (core.iter.range.IteratorRange.next_Usize_some_spec iter (by rwa [stop]))
    rw [someEq] at read
    have body := pivot_row_refines kernels law degree width column rows witnesses vector witness
      iter next layout active read
    cases step : pivotRow degree.val column.val rows witnesses iter.start.val vector witness with
    | none =>
      refine ⟨vector, witness, some iter.start, ?_, ?_, layout, ?_⟩
      · unfold multiple_loop0_loop0 loop
        dsimp only
        simp only [body, step, bind_ok]
      · simp only [pivotSearch, step, Option.map_some]
      · intro index equal
        obtain rfl := Option.some.inj equal.symm
        refine ⟨Nat.le_refl _, active, ?_⟩
        unfold pivotRow at step
        split at step
        · contradiction
        · rename_i nonzero
          split at step
          · rename_i vacant
            exact ⟨vacant, nonzero⟩
          · contradiction
    | some updated =>
      rcases updated with ⟨nextVector, nextWitness⟩
      have nextLayout := continue_layout layout iter.start.val (nextVector, nextWitness) step
      obtain ⟨finalVector, finalWitness, pivot, run, model, finalLayout, pivotMeaning⟩ :=
        ih next nextVector nextWitness (by omega) (nextStop.trans stop) nextLayout
      refine ⟨finalVector, finalWitness, pivot, ?_, ?_, finalLayout, ?_⟩
      · unfold multiple_loop0_loop0 loop
        dsimp only
        simpa only [body, step, bind_ok, multiple_loop0_loop0] using run
      · simp only [pivotSearch, step, ← advanced, model]
      · intro index found
        obtain ⟨lower, upper, empty, nonzero⟩ := pivotMeaning index found
        exact ⟨by omega, upper, empty, nonzero⟩

end BulksketchBridge.AffineMultiple
