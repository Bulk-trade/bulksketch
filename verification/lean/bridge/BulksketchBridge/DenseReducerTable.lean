import BulksketchBridge.DenseReducerTableSpec
import BulksketchBridge.TimesXMod
import BulksketchBridge.BmStepControl
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.DenseReducerTable

open Aeneas Aeneas.Std Algebra.Gf64 DenseCoefficient TimesXMod RebuiltLfsr
open bulksketch.backend.contract
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

set_option maxRecDepth 4096
set_option maxHeartbeats 1300000

@[simp] theorem stepWords_length (modulus current : Slice U64) :
    (stepWords modulus current).length = current.length := by
  simp only [stepWords, Slice.length, Slice.from_val, List.length_ofFn]

theorem stepWords_word (modulus current : Slice U64) (index : Nat)
    (bound : index < current.length) :
    (stepWords modulus current)[index]! =
      (shiftedWords current)[index]! ^^^
        (⟨multiplyWord current[current.length - 1]!.bv
          (prefixSlice modulus current.length)[index]!.bv⟩ : U64) := by
  simp only [stepWords, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ index (by simpa using bound), List.getElem_ofFn]

theorem stepWords_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : ExactScaleXor kernels) (modulus current : Slice U64)
    (positive : 0 < current.length) (room : current.length ≤ modulus.length) :
    bulksketch.poly.dense.times_x_mod fieldDictionary kernels current modulus =
      .ok (stepWords modulus current) := by
  rw [times_x_mod_refines _ _ _ _ positive room]
  let shifted := shiftedWords current
  let low := prefixSlice modulus current.length
  let scale := current[current.length - 1]!
  change kernels.ArithmeticInst.scale_xor shifted low scale = _
  have shiftLen : shifted.length = current.length := shifted_length _
  have lowLen : low.length = current.length :=
    (prefix_length _ _).trans (Nat.min_eq_left room)
  obtain ⟨out, called, len, words⟩ := arithmetic shifted low scale (shiftLen.trans lowLen.symm)
  rw [called]
  congr 1
  apply Slice.ext_getElem (by rw [stepWords_length, len, shiftLen])
  intro i left right
  have bounded : i < current.length := by rwa [← shiftLen, ← len]
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ left,
    Slice.Inhabited_getElem_eq_getElem! _ _ right, stepWords_word modulus current i bounded]
  exact words i (by rwa [shiftLen])

@[simp] theorem initialWords_length (modulus : Slice U64) (degree : Nat) (room : degree ≤ modulus.length) :
    (initialWords modulus degree).length = degree := by
  by_cases even : degree % 2 = 0 <;>
    simp only [initialWords, even, ite_true, ite_false, stepWords_length,
      prefix_length, Nat.min_eq_left room]

private theorem loop_step {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : ExactScaleXor kernels)
    (modulus table current : Slice U64) (degree rows : Usize)
    (iter next : BmStepControl.IndexRange)
    (read : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some iter.start, next))
    (degreePos : 0 < degree.val) (currentLen : current.length = degree.val)
    (modRoom : degree.val ≤ modulus.length)
    (rowBound : iter.start.val < rows.val) (tableRoom : rows.val * degree.val ≤ table.length) :
    prepare_square_table_loop.body fieldDictionary kernels modulus degree rows iter table current =
      .ok (.cont (next, table.setSlice! (iter.start.val * degree.val) current.val,
        if iter.start.val + 1 = rows.val then current else stepWords modulus (stepWords modulus current))) := by
  have tableMax : table.length ≤ Usize.max := table.length_ineq
  have rowsMax : rows.val ≤ Usize.max := by scalar_tac
  have startBound : iter.start.val * degree.val ≤ table.length :=
    (Nat.mul_le_mul_right degree.val (by omega : iter.start.val ≤ rows.val)).trans tableRoom
  have stopBound : (iter.start.val + 1) * degree.val ≤ table.length :=
    (Nat.mul_le_mul_right degree.val (by omega : iter.start.val + 1 ≤ rows.val)).trans tableRoom
  obtain ⟨first, firstNormal, firstVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := iter.start) (y := degree) (by omega))
  obtain ⟨succ, succNormal, succVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := iter.start) (y := 1#usize) (by
      change iter.start.val + 1 ≤ Usize.max
      omega))
  change succ.val = iter.start.val + 1 at succVal
  obtain ⟨last, lastNormal, lastVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := succ) (y := degree) (by rw [succVal]; omega))
  change first.val = iter.start.val * degree.val at firstVal
  change last.val = succ.val * degree.val at lastVal
  rw [succVal, Nat.add_mul, Nat.one_mul] at lastVal
  have order : first.val ≤ last.val := by omega
  have bounded : last.val ≤ table.length := by
    simpa only [lastVal, Nat.add_mul, Nat.one_mul] using stopBound
  have indexNormal := ClosedLeaf.mutable_region_normal table first last order bounded
  have copyLen : (ClosedLeaf.region table first.val last.val).length = current.length := by
    rw [ClosedLeaf.region_length _ _ _ bounded]
    omega
  have copy := ClosedLeaf.copy_normal (ClosedLeaf.region table first.val last.val) current copyLen
  have shift := stepWords_refines kernels arithmetic modulus current (by omega) (by omega)
  have shiftAgain := stepWords_refines kernels arithmetic modulus (stepWords modulus current)
    (by simp only [stepWords_length]; omega) (by simp only [stepWords_length]; omega)
  simp only [prepare_square_table_loop.body, read, bind_ok]
  try dsimp! only
  simp only [firstNormal, succNormal, lastNormal, Slice.index_mut_SliceIndexRangeUsizeSliceInst,
    indexNormal, bind_ok]
  try dsimp! only
  simp only [copy, bind_ok]
  rw [firstVal]
  by_cases final : iter.start.val + 1 = rows.val
  · have equal : succ = rows := UScalar.eq_of_val_eq (succVal.trans final)
    simp [equal, final]
  · have different : succ ≠ rows := by
      intro equal
      exact final (succVal.symm.trans (congrArg UScalar.val equal))
    have test : (succ != rows) = true := by simp [different]
    simp only [test, ite_true, final, ite_false, shift, shiftAgain, bind_ok]

theorem loop_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : ExactScaleXor kernels) (modulus : Slice U64) (degree rows : Usize)
    (degreePos : 0 < degree.val) (modRoom : degree.val ≤ modulus.length)
    (count : Nat) (iter : BmStepControl.IndexRange) (table current : Slice U64)
    (stop : iter.end = rows) (remaining : iter.start.val + count = rows.val)
    (currentLen : current.length = degree.val) (tableRoom : rows.val * degree.val ≤ table.length) :
    prepare_square_table_loop fieldDictionary kernels iter modulus table degree rows current =
      .ok (fillRows modulus degree.val table current iter.start.val count) := by
  induction count generalizing iter table current with
  | zero =>
    obtain ⟨⟨out, next⟩, read, none, exactNext⟩ := RawMulTable.normal_of_spec _ _
      (core.iter.range.IteratorRange.next_Usize_none_spec iter (by rw [stop]; omega))
    have body :
        prepare_square_table_loop.body fieldDictionary kernels modulus degree rows iter table current =
          .ok (.done (table, current)) := by
      rw [none] at read
      simp only [prepare_square_table_loop.body, read, bind_ok]
      rfl
    conv => lhs; unfold prepare_square_table_loop loop
    simp only [body, bind_ok, fillRows]
  | succ count ih =>
    have active : iter.start.val < iter.end.val := by rw [stop]; omega
    obtain ⟨⟨out, next⟩, read, some, advanced, nextStop⟩ := RawMulTable.normal_of_spec _ _
      (core.iter.range.IteratorRange.next_Usize_some_spec iter active)
    rw [some] at read
    let written := table.setSlice! (iter.start.val * degree.val) current.val
    let advancedWords := if count = 0 then current else stepWords modulus (stepWords modulus current)
    have frame : advancedWords.length = degree.val := by
      by_cases final : count = 0 <;> simp [advancedWords, final, currentLen]
    have isFinal : (iter.start.val + 1 = rows.val) ↔ count = 0 := by omega
    have body :=
      loop_step kernels arithmetic modulus table current degree rows iter next read
        degreePos currentLen modRoom (by omega) tableRoom
    simp only [isFinal] at body
    have recursed := ih next written advancedWords (nextStop.trans stop) (by rw [advanced]; omega)
      frame (by simpa [written] using tableRoom)
    conv => lhs; unfold prepare_square_table_loop loop
    simp only [body, bind_ok, fillRows]
    change prepare_square_table_loop fieldDictionary kernels next modulus written degree rows advancedWords = _
    simpa only [advanced] using recursed

/-- The original wrapper keeps both bounds assertions and the exact
monic check, restores only the active work prefix, and writes all rows. -/
theorem prepare_square_table_refines : ActualPrepareSquareTable := by
  intro K kernels arithmetic modulus table work minLen monic tableRoom workRoom
  let degreeNat := modulus.length - 1
  have modMax : modulus.length ≤ Usize.max := modulus.length_ineq
  have workMax : work.length ≤ Usize.max := work.length_ineq
  have tableMax : table.length ≤ Usize.max := table.length_ineq
  have minCheck : (4#usize : Usize) ≤ Slice.len modulus := by scalar_tac
  obtain ⟨degree, degreeNormal, degreeValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := Slice.len modulus) (y := 1#usize) (by scalar_tac))
  rw [Slice.len_val] at degreeValue
  change degree.val = degreeNat at degreeValue
  obtain ⟨rows, rowsNormal, rowsValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec degree (y := 2#usize) (by simp))
  change rows.val = degree.val / 2 at rowsValue
  have tableBound : degree.val * rows.val ≤ table.length := by
    rw [rowsValue, degreeValue]
    exact tableRoom
  obtain ⟨tableLen, tableNormal, tableValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := degree) (y := rows) (tableBound.trans tableMax))
  have tableCheck : tableLen ≤ Slice.len table := by
    change tableLen.val ≤ (Slice.len table).val
    rw [tableValue, Slice.len_val]
    exact tableBound
  obtain ⟨width, widthNormal, widthValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := degree) (y := 1#usize) (by
      change degree.val + 1 ≤ Usize.max
      rw [degreeValue]
      dsimp only [degreeNat]
      omega))
  have widthExact : width.val = modulus.length := by
    change width.val = degree.val + 1 at widthValue
    rw [widthValue, degreeValue]
    dsimp only [degreeNat]
    omega
  obtain ⟨workLen, workNormal, workValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := 4#usize) (y := width) (by
      change 4 * width.val ≤ Usize.max
      rw [widthExact]
      exact workRoom.trans workMax))
  have workCheck : workLen ≤ Slice.len work := by
    change workLen.val ≤ (Slice.len work).val
    rw [workValue, Slice.len_val, widthExact]
    exact workRoom
  have last : bulksketch.DenseReducerTableRuntime.last modulus = .ok (some 1#u64) := by
    unfold bulksketch.DenseReducerTableRuntime.last
    rw [List.getLast?_eq_getElem?]
    have inRange : modulus.val.length - 1 < modulus.val.length := by
      change modulus.length - 1 < modulus.length
      omega
    rw [List.getElem?_eq_getElem inRange]
    rw [List.Inhabited_getElem_eq_getElem! _ _ inRange, ← Slice.getElem!_Nat_eq]
    exact congrArg (fun v => Result.ok (some v)) monic
  have compare : bulksketch.DenseReducerTableRuntime.optionEq
      (core.cmp.PartialEqShared core.cmp.PartialEqU64) (some 1#u64) (some 1#u64) = .ok true := by
    rfl
  have degreePos : 0 < degree.val := by rw [degreeValue]; dsimp only [degreeNat]; omega
  have modRoom : degree.val ≤ modulus.length := by rw [degreeValue]; dsimp only [degreeNat]; omega
  have workBound : degree.val ≤ work.length := by rw [degreeValue]; dsimp only [degreeNat]; omega
  have workPrefix := prefix_normal work degree workBound
  have modPrefix := shared_prefix_normal modulus degree modRoom
  have copyLen : (prefixSlice work degree.val).length = (prefixSlice modulus degree.val).length := by
    rw [prefix_length, prefix_length, Nat.min_eq_left workBound, Nat.min_eq_left modRoom]
  have copied := ClosedLeaf.copy_normal _ _ copyLen
  have lowLen : (prefixSlice modulus degree.val).length = degree.val :=
    (prefix_length _ _).trans (Nat.min_eq_left modRoom)
  have initial : (if degree.val % 2 == 0 then
       Result.ok (prefixSlice modulus degree.val)
    else bulksketch.poly.dense.times_x_mod fieldDictionary kernels (prefixSlice modulus degree.val) modulus) =
      .ok (initialWords modulus degree.val) := by
    rw [stepWords_refines kernels arithmetic modulus (prefixSlice modulus degree.val)
      (by omega) (by omega)]
    by_cases even : degree.val % 2 = 0 <;> simp [initialWords, even]
  have rowsResult := loop_refines kernels arithmetic modulus degree rows degreePos modRoom rows.val
    ⟨0#usize, rows⟩ table (initialWords modulus degree.val) rfl
    (by change 0 + rows.val = rows.val; omega)
    (initialWords_length modulus degree.val modRoom)
    (by simpa only [Nat.mul_comm rows.val degree.val] using tableBound)
  simp only [prepare_square_table, minCheck, massert, ite_true, last, bind_ok, compare,
    degreeNormal, rowsNormal, tableNormal, tableCheck, widthNormal, workNormal, workCheck,
    Slice.index_mut_SliceIndexRangeToUsizeSliceInst, workPrefix, Slice.index_SliceIndexRangeToUsizeSliceInst,
    modPrefix]
  try dsimp! only
  simp only [copied, bind_ok, core.num.Usize.is_multiple_of, UScalar.is_multiple_of]
  change (do
    let current ← (if degree.val % 2 == 0 then Result.ok (prefixSlice modulus degree.val)
      else bulksketch.poly.dense.times_x_mod fieldDictionary kernels (prefixSlice modulus degree.val) modulus)
    let (updated, words) ← prepare_square_table_loop fieldDictionary kernels
      ⟨0#usize, rows⟩ modulus table degree rows current
    Result.ok (updated, restorePrefix work words)) = _
  simp only [initial, Bind.bind, bind_ok, rowsResult]
  simp only [expectedTable, rowsValue, degreeValue, degreeNat, restorePrefix]
  rfl

end BulksketchBridge.DenseReducerTable
