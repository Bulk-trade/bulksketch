import BulksketchBridge.DenseDivRemRows

namespace BulksketchBridge.DenseDivRem

open Aeneas Aeneas.Std BulksketchBridge BulksketchBridge.MutableZip
open BulksketchBridge.DenseMulConvolutionSpec
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096

def window (raw : Slice Raw) (start stop : Nat) : Slice Raw :=
  Slice.from (raw.val.slice start stop)
    (Nat.le_trans (List.slice_length_le start stop raw.val) (Slice.length_ineq raw))

theorem window_length (raw : Slice Raw) (start stop : Nat) (room : stop ≤ raw.length) :
    (window raw start stop).length = stop - start := by
  simp only [window, Slice.length, Slice.from_val, List.slice_length]
  exact Nat.min_eq_right (Nat.sub_le_sub_right room start)

theorem cut_window (raw : Slice Raw) (start stop : Usize)
    (ordered : start.val ≤ stop.val) (room : stop.val ≤ raw.length) :
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut ⟨start, stop⟩ raw =
      .ok (window raw start.val stop.val, fun replacement : Slice Raw => raw.setSlice! start.val replacement.val) := by
  have order' : start ≤ stop := by scalar_tac
  obtain ⟨⟨win, back⟩, normal, payload, _, backEq⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec ⟨start, stop⟩ raw order' room)
  rw [normal, show win = window raw start.val stop.val from
    Slice.ext _ _ (by simpa only [window, Slice.from_val] using payload), funext backEq]

private theorem restore_window (raw : Slice Raw) (b : Slice U64) (factor : U64)
    (start stop degree : Usize) (ordered : start.val ≤ stop.val)
    (room : stop.val ≤ raw.length) (same : stop.val - start.val = degree.val)
    (_bRoom : degree.val ≤ b.length)
    (f : Raw → U64 → Raw)
    (update : ∀ old i, start.val ≤ i → i < stop.val →
      DenseDivision.updateWord b factor start.val stop.val i old =
        f old b[i - start.val]!) :
    raw.setSlice! start.val
      (mapFrom (window raw start.val stop.val) (DenseCoefficient.prefixSlice b degree.val) f 0).val =
      DenseDivision.updateRaw b factor start.val stop.val raw := by
  let win := window raw start.val stop.val
  let right := DenseCoefficient.prefixSlice b degree.val
  let mapped := mapFrom win right f 0
  have winLen : win.length = degree.val := (window_length raw start.val stop.val room).trans same
  have mappedLength : mapped.val.length = degree.val := by
    change mapped.length = degree.val
    exact (mapFrom_length _ _ _ _).trans winLen
  apply Slice.ext_getElem (by simp [DenseDivision.update_raw_length])
  intro slot restoredBound outputBound
  have slotBound : slot < raw.length := by simpa [DenseDivision.update_raw_length] using outputBound
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ restoredBound,
    Slice.Inhabited_getElem_eq_getElem! _ _ outputBound, DenseDivision.update_raw_word _ _ _ _ _ _ slotBound]
  change (raw.setSlice! start.val mapped.val)[slot]! = _
  by_cases inside : start.val ≤ slot ∧ slot < stop.val
  · rw [update _ _ inside.1 inside.2,
      Slice.setSlice!_getElem!_middle raw mapped.val start.val slot (by rw [mappedLength]; omega)]
    rw [← Slice.getElem!_Nat_eq]
    change (mapFrom win right f 0)[slot - start.val]! = _
    rw [mapFrom_word _ _ _ _ _ (by omega), ite_eq_left (Nat.zero_le _)]
    have old : win[slot - start.val]! = raw[slot]! := by
      simp only [win, window, Slice.getElem!_Nat_eq, Slice.from_val]
      rw [List.getElem!_slice start.val stop.val (slot - start.val) raw.val (by
        change stop.val ≤ raw.length ∧ start.val + (slot - start.val) < stop.val
        omega), show start.val + (slot - start.val) = slot by omega]
    have coefficient : right[slot - start.val]! = b[slot - start.val]! := by
      change (DenseMul.takeSlice b degree.val)[slot - start.val]! = _
      exact DenseMul.take_word _ _ _ (by omega)
    rw [old, coefficient]
  · simp only [DenseDivision.updateWord, inside, ite_false]
    by_cases before : slot < start.val
    · exact Slice.setSlice!_getElem!_prefix raw mapped.val start.val slot before
    · exact Slice.setSlice!_getElem!_suffix raw mapped.val start.val slot (by rw [mappedLength]; omega)

theorem unit_restore (raw : Slice Raw) (b : Slice U64)
    (start stop degree : Usize) (ordered : start.val ≤ stop.val)
    (room : stop.val ≤ raw.length) (same : stop.val - start.val = degree.val)
    (bRoom : degree.val ≤ b.length) :
    raw.setSlice! start.val
      (mapFrom (window raw start.val stop.val) (DenseCoefficient.prefixSlice b degree.val) unitWord 0).val =
      DenseDivision.updateRaw b 1#u64 start.val stop.val raw := by
  apply restore_window raw b 1#u64 start stop degree ordered room same bRoom unitWord
  intro old i hlo hhi
  simp only [DenseDivision.updateWord, hlo, hhi, and_self, ite_true,
    show (1#u64 : U64) ≠ 0#u64 by decide, ite_false, unitWord]

theorem product_restore (raw : Slice Raw) (b : Slice U64) (factor : U64)
    (start stop degree : Usize) (ordered : start.val ≤ stop.val)
    (room : stop.val ≤ raw.length) (same : stop.val - start.val = degree.val)
    (bRoom : degree.val ≤ b.length) (zero : factor ≠ 0#u64) (unit : factor ≠ 1#u64) :
    raw.setSlice! start.val
      (mapFrom (window raw start.val stop.val) (DenseCoefficient.prefixSlice b degree.val) (productWord factor) 0).val =
      DenseDivision.updateRaw b factor start.val stop.val raw := by
  apply restore_window raw b factor start stop degree ordered room same bRoom (productWord factor)
  intro old i hlo hhi
  simp only [DenseDivision.updateWord, hlo, hhi, and_self, ite_true, zero, unit, ite_false, productWord]

theorem row_lengths (raw : Slice Raw) (b : Slice U64) (start stop degree : Usize)
    (room : stop.val ≤ raw.length) (same : stop.val - start.val = degree.val)
    (bRoom : degree.val ≤ b.length) :
    (window raw start.val stop.val).length = (DenseCoefficient.prefixSlice b degree.val).length := by
  rw [window_length _ _ _ room, same, RebuiltLfsr.prefix_length, Nat.min_eq_left bRoom]

/-- The common subexpression in the four original active row branches.
The returned loop continuation is applied to the returned terminal Zip
before the pinned Zip, IterMut, and slice write-backs. -/
def rowCall {α : Type} (run : Zip → Back → Result (Zip × Back)) (raw : Slice Raw) (b : Slice U64)
    (start stop degree : Usize) (finish : Slice Raw → α) : Result α := do
  let (region, restoreRegion) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice Raw) raw ⟨start, stop⟩
  let (iterator, restoreIterator) ← core.slice.Slice.iter_mut region
  let coefficients ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeToUsizeSlice U64) b ⟨degree⟩
  let (zipped, restoreZip) ← bulksketch.core.iter.traits.iterator.Iterator.zip.trait_default
    (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT Raw)
    (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64) iterator coefficients
  let (terminal, back) ← run zipped (fun z => z)
  .ok (finish (restoreRegion (restoreIterator (restoreZip (back terminal)))))

def RowLoop (run : Zip → Back → Result (Zip × Back)) (transform : Raw → U64 → Raw) : Prop :=
  ∀ left right, left.length = right.length →
    ∃ back, run (stateAt left right 0) (fun z => z) = .ok (stateAt left right left.length, back) ∧
      back (stateAt left right left.length) = stateAt (mapFrom left right transform 0) right left.length

private theorem row_call_normal {α : Type} (run : Zip → Back → Result (Zip × Back))
    (transform : Raw → U64 → Raw) (loopLaw : RowLoop run transform)
    (raw : Slice Raw) (b : Slice U64) (start stop degree : Usize)
    (ordered : start.val ≤ stop.val) (room : stop.val ≤ raw.length)
    (same : stop.val - start.val = degree.val) (bRoom : degree.val ≤ b.length) (finish : Slice Raw → α) :
    rowCall run raw b start stop degree finish =
      .ok (finish (raw.setSlice! start.val
        (mapFrom (window raw start.val stop.val) (DenseCoefficient.prefixSlice b degree.val) transform 0).val)) := by
  let left := window raw start.val stop.val
  let right := DenseCoefficient.prefixSlice b degree.val
  obtain ⟨back, ran, writes⟩ := loopLaw left right (row_lengths raw b start stop degree room same bRoom)
  simp only [rowCall, Slice.index_mut_SliceIndexRangeUsizeSliceInst,
    cut_window raw start stop ordered room, Slice.index_SliceIndexRangeToUsizeSliceInst,
    RebuiltLfsr.shared_prefix_normal b degree bRoom, core.slice.Slice.iter_mut, bind_ok]
  dsimp! only
  rw [construct left right]
  simp only [bind_ok]
  dsimp! only
  rw [ran, bind_ok]
  dsimp! only
  rw [writes]
  rfl

theorem unit_row_call {α : Type} (run : Zip → Back → Result (Zip × Back)) (loopLaw : RowLoop run unitWord)
    (raw : Slice Raw) (b : Slice U64) (start stop degree : Usize)
    (ordered : start.val ≤ stop.val) (room : stop.val ≤ raw.length)
    (same : stop.val - start.val = degree.val) (bRoom : degree.val ≤ b.length) (finish : Slice Raw → α) :
    rowCall run raw b start stop degree finish = .ok (finish (DenseDivision.updateRaw b 1#u64 start.val stop.val raw)) := by
  rw [row_call_normal run unitWord loopLaw raw b start stop degree ordered room same bRoom finish,
    unit_restore raw b start stop degree ordered room same bRoom]

theorem product_row_call {α : Type} (run : Zip → Back → Result (Zip × Back)) (factor : U64)
    (loopLaw : RowLoop run (productWord factor))
    (raw : Slice Raw) (b : Slice U64) (start stop degree : Usize)
    (ordered : start.val ≤ stop.val) (room : stop.val ≤ raw.length)
    (same : stop.val - start.val = degree.val) (bRoom : degree.val ≤ b.length)
    (zero : factor ≠ 0#u64) (unit : factor ≠ 1#u64) (finish : Slice Raw → α) :
    rowCall run raw b start stop degree finish = .ok (finish (DenseDivision.updateRaw b factor start.val stop.val raw)) := by
  rw [row_call_normal run (productWord factor) loopLaw raw b start stop degree ordered room same bRoom finish,
    product_restore raw b factor start stop degree ordered room same bRoom zero unit]

end BulksketchBridge.DenseDivRem
