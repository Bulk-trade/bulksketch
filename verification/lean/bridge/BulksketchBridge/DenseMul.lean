import BulksketchBridge.DenseMulSpec
import BulksketchBridge.DenseMulConvolution
import BulksketchBridge.DenseMulReduction
import BulksketchBridge.DenseNormalization

namespace BulksketchBridge.DenseMul

open Aeneas Aeneas.Std Aeneas.Std.WP DenseMulConvolutionSpec MutableZip
open DenseMulReductionSpec (reduceWord)
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial
open scoped BulksketchBridge.DenseMulReductionSpec

@[simp] theorem take_length {T : Type} (buffer : Slice T) (count : Nat) :
    (takeSlice buffer count).length = min count buffer.length := by simp [takeSlice, Slice.length]

theorem take_word {T : Type} [Inhabited T] (buffer : Slice T) (count index : Nat) (bound : index < count) :
    (takeSlice buffer count)[index]! = buffer[index]! := by
  simp only [takeSlice, Slice.getElem!_Nat_eq, Slice.from_val,
    List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt bound]

private theorem cut_mut {T : Type} (buffer : Slice T) (stop : Usize) (bound : stop.val ≤ buffer.length) :
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut ⟨stop⟩ buffer =
      Result.ok (takeSlice buffer stop.val, fun (replacement : Slice T) => buffer.setSlice! 0 replacement.val) := by
  obtain ⟨⟨window, restore⟩, normal, values, _, update⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec ⟨stop⟩ buffer bound)
  have windowEq : window = takeSlice buffer stop.val := by
    rw [Slice.eq_iff]
    simpa only [takeSlice, Slice.from_val, List.slice_zero_j] using values
  have restoreEq : restore = fun (replacement : Slice T) => buffer.setSlice! 0 replacement.val := by
    funext replacement
    rw [Slice.eq_iff]
    simpa only [Slice.setSlice!_val] using update replacement
  rw [normal, windowEq, restoreEq]

private theorem cut {T : Type} (buffer : Slice T) (stop : Usize) (bound : stop.val ≤ buffer.length) :
    core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨stop⟩ buffer =
      Result.ok (takeSlice buffer stop.val) := by
  obtain ⟨window, normal, values, _⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec ⟨stop⟩ buffer bound)
  have windowEq : window = takeSlice buffer stop.val := by
    rw [Slice.eq_iff]
    simpa only [takeSlice, Slice.from_val, List.slice_zero_j] using values
  rw [normal, windowEq]

private theorem fill_raw (window : Slice Raw) :
    core.slice.Slice.fill bulksketch.types.RawProduct.Insts.CoreCloneClone window zeroProduct =
      Result.ok (Slice.from (List.replicate window.length zeroProduct) (by simp)) := by
  obtain ⟨zeros, normal, length, values⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.Slice.fill.spec bulksketch.types.RawProduct.Insts.CoreCloneClone window zeroProduct
      (by exact (WP.spec_ok zeroProduct).mpr rfl))
  have zerosEq : zeros = Slice.from (List.replicate window.length zeroProduct) (by simp) := by
    rw [Slice.eq_iff]
    simpa [length] using values
  rw [normal, zerosEq]

private theorem default_raw :
    bulksketch.types.RawProduct.Insts.CoreDefaultDefault.default = Result.ok zeroProduct := rfl

/-- Compose the original wrapper with its independently proved convolution loop. -/
theorem mul_into_refines : ActualDenseMulReturnsExactFrames := by
  intro K kernels rawMul reduce a b dst raw
  by_cases leftEmpty : a.length = 0
  · simp [leftEmpty, mul_into]
  by_cases rightEmpty : b.length = 0
  · simp [leftEmpty, rightEmpty, mul_into]
  rw [ite_eq_right (not_or.mpr ⟨leftEmpty, rightEmpty⟩)]
  by_cases machine : a.length + b.length ≤ Usize.max
  · rw [ite_eq_left machine]
    obtain ⟨size, sizeNormal, sizeValue⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := a.len) (y := b.len) (by simpa using machine))
    have exactSize : size.val = a.length + b.length := by simpa using sizeValue
    by_cases room : a.length + b.length ≤ dst.length ∧ a.length + b.length ≤ raw.length
    · rw [ite_eq_left room]
      have dstGuard : size ≤ dst.len := by rw [UScalar.le_equiv, Slice.len_val, exactSize]; exact room.1
      have rawGuard : size ≤ raw.len := by rw [UScalar.le_equiv, Slice.len_val, exactSize]; exact room.2
      obtain ⟨stop, stopNormal, stopValue⟩ := RawMulTable.normal_of_spec _ _
        (Usize.sub_spec (x := size) (y := 1#usize) (by
          change 1 ≤ size.val
          omega))
      have count : stop.val = a.length + b.length - 1 := by simpa [exactSize] using stopValue.1
      have rawRoom : stop.val ≤ raw.length := by omega
      have dstRoom : stop.val ≤ dst.length := by omega
      have rawCut := cut_mut raw stop rawRoom
      have dstCut := cut_mut dst stop dstRoom
      have windowLength : (takeSlice raw stop.val).length = stop.val := by
        simp [Nat.min_eq_left rawRoom]
      have rawFill := fill_raw (takeSlice raw stop.val)
      have clearedRoom : a.length + b.length ≤ (clearedRaw raw stop.val).length := by
        simpa [clearedRaw] using room.2
      have outerNormal := DenseMulConvolution.outer_loop_refines kernels rawMul a b (clearedRaw raw stop.val) 0#usize (by simp) clearedRoom
      have finishedLength : (finishedRaw a b raw).length = raw.length := by simp [finishedRaw, clearedRaw]
      have resultRoom : stop.val ≤ (finishedRaw a b raw).length := by omega
      have rawRead := cut (finishedRaw a b raw) stop resultRoom
      let dstWindow := takeSlice dst stop.val
      let rawWindow := takeSlice (finishedRaw a b raw) stop.val
      have dstWindowLen : dstWindow.length = stop.val := by simp [dstWindow, Nat.min_eq_left dstRoom]
      have rawWindowLen : rawWindow.length = stop.val := by simp [rawWindow, Nat.min_eq_left resultRoom]
      obtain ⟨restore, reduceNormal, restored⟩ := DenseMulReduction.loop_refines
        kernels reduce dstWindow rawWindow (dstWindowLen.trans rawWindowLen.symm)
        0 (Nat.zero_le _) (fun state => state)
      have outLen : (finishedDst a b dst raw).length = dst.length := by simp [finishedDst]
      have outRoom : stop.val ≤ (finishedDst a b dst raw).length := by omega
      have outRead := cut (finishedDst a b dst raw) stop outRoom
      obtain ⟨normalized, normNormal, normValue⟩ :=
        DenseNormalization.normalized_len_refines (takeSlice (finishedDst a b dst raw) stop.val)
      refine ⟨normalized, ?_, ?_⟩
      · simp only [mul_into, core.slice.Slice.is_empty, leftEmpty, rightEmpty, decide_false,
          Bool.false_eq_true, ite_false, bind_ok, sizeNormal, massert, dstGuard, rawGuard, ite_true,
          stopNormal, Slice.index_mut_SliceIndexRangeToUsizeSliceInst, rawCut]
        dsimp! only
        simp only [default_raw, bind_ok, rawFill, core.slice.Slice.iter]
        have start : core.iter.traits.iterator.Iterator.enumerate.trait_default
            (core.iter.traits.iterator.IteratorSliceIter U64) ⟨a, 0⟩ =
            Result.ok (iteratorAt a 0#usize) := rfl
        simp only [start, bind_ok]
        have cleared : (raw.setSlice! 0
            (Slice.from (List.replicate (takeSlice raw stop.val).length zeroProduct) (by simp)).val) =
            clearedRaw raw stop.val := by simp [clearedRaw, windowLength]
        rw [cleared, outerNormal]
        simp only [bind_ok]
        have rawExact : accumulateRows a b (clearedRaw raw stop.val) 0 a.length = finishedRaw a b raw := by
          rw [count]; rfl
        simp only [show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero, rawExact, dstCut, bind_ok]
        dsimp! only
        simp only [core.slice.Slice.iter_mut, Slice.index_SliceIndexRangeToUsizeSliceInst, rawRead, bind_ok]
        dsimp! only
        rw [MutableZip.construct]
        simp only [bind_ok]
        dsimp! only
        have reduceExact : mul_into_loop1 dictionary kernels
            (stateAt dstWindow rawWindow 0) (fun state => state) =
            Result.ok (stateAt dstWindow rawWindow dstWindow.length, restore) := reduceNormal
        rw [reduceExact]
        simp only [bind_ok]
        dsimp! only
        rw [restored]
        have outputExact :
            dst.setSlice! 0 (mapFrom dstWindow rawWindow (fun _ product => reduceWord product) 0).val =
              finishedDst a b dst raw := by
          simp only [dstWindow, rawWindow, count, finishedDst]
        simp only [stateAt, outputExact, outRead, normNormal, bind_ok]
      · simpa only [takeSlice, Slice.from_val, count] using normValue
    · rw [ite_eq_right room]
      by_cases dstRoom : a.length + b.length ≤ dst.length
      · have dstGuard : size ≤ dst.len := by rw [UScalar.le_equiv, Slice.len_val, exactSize]; exact dstRoom
        have rawGuard : ¬ size ≤ raw.len := by
          rw [UScalar.le_equiv, Slice.len_val, exactSize]
          exact fun enough => room ⟨dstRoom, enough⟩
        simp only [mul_into, core.slice.Slice.is_empty, leftEmpty, rightEmpty, decide_false,
          Bool.false_eq_true, ite_false, sizeNormal, massert, dstGuard, rawGuard, ite_true, bind_ok, bind_fail]
      · have dstGuard : ¬ size ≤ dst.len := by
          rw [UScalar.le_equiv, Slice.len_val, exactSize]
          exact dstRoom
        simp only [mul_into, core.slice.Slice.is_empty, leftEmpty, rightEmpty, decide_false,
          Bool.false_eq_true, ite_false, sizeNormal, massert, dstGuard, bind_ok, bind_fail]
  · rw [ite_eq_right machine]
    have overflow : a.len + b.len = Result.fail Error.integerOverflow := by
      change UScalar.add a.len b.len = _
      unfold UScalar.add UScalar.tryMk UScalar.tryMkOpt
      have invalid : ¬ UScalar.check_bounds .Usize (a.len.val + b.len.val) := by
        intro bound
        have bounds := UScalar.check_bounds_imp_inBounds bound
        change a.len.val + b.len.val < 2 ^ UScalarTy.Usize.numBits at bounds
        simp only [Slice.len_val] at bounds
        apply machine
        rw [Usize.max, Usize.numBits]
        omega
      rw [dite_eq_right invalid]
      rfl
    simp [mul_into, leftEmpty, rightEmpty, overflow, bind_fail]

end BulksketchBridge.DenseMul
