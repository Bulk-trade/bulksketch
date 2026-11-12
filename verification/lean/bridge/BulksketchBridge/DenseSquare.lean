import BulksketchBridge.DenseSquareChallenges
import BulksketchBridge.DenseSquareLoop
import BulksketchBridge.DenseNormalization
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.DenseSquare

open Aeneas Aeneas.Std
open DenseSquareChallenges
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

private theorem restored_frame (a dst zeros window output : Slice U64)
    (zeroLength : zeros.length = 2 * a.length)
    (zeroValues : zeros.val = List.replicate zeros.length 0#u64)
    (dstBound : 2 * a.length ≤ dst.length)
    (windowValues : window.val = (dst.val.setSlice! 0 zeros.val).take (2 * a.length))
    (outputValues : output.val =
      (dst.val.setSlice! 0 zeros.val).setSlice! 0 (squareFrom window a 0).val) :
    output.length = dst.length ∧
      ∀ i, i < dst.length → output[i]! = coefficient a dst i := by
  have zeroListLength : zeros.val.length = 2 * a.length := zeroLength
  have dstListBound : 2 * a.length ≤ dst.val.length := dstBound
  have windowExact : window.val = zeros.val := by
    rw [windowValues, List.setSlice!]
    simp only [List.take_zero, List.nil_append, Nat.sub_zero, Nat.zero_add,
      min_eq_left (show zeros.val.length ≤ dst.val.length by omega),
      List.take_length]
    rw [List.take_append_of_le_length (by omega), ← zeroListLength, List.take_length]
  have windowLength : window.length = 2 * a.length := by
    change window.val.length = _
    rw [windowExact, zeroListLength]
  have processedLength : (squareFrom window a 0).val.length = 2 * a.length := by
    change (squareFrom window a 0).length = _
    rw [squareFrom_length, windowLength]
  refine ⟨by change output.val.length = dst.val.length; simp [outputValues], ?_⟩
  intro i bounded
  rw [Slice.getElem!_Nat_eq, outputValues]
  unfold coefficient
  by_cases inside : i < 2 * a.length
  · have inUpdated : i < (dst.val.setSlice! 0 zeros.val).length := by
      rw [List.length_setSlice!]
      exact bounded
    rw [ite_eq_left inside, List.getElem!_setSlice!_middle _ _ _ _
      ⟨Nat.zero_le _, by omega, inUpdated⟩, Nat.sub_zero, ← Slice.getElem!_Nat_eq,
      squareFrom_word window a 0 i (by omega)]
    by_cases even : i % 2 = 0
    · simp [even]
    · simp only [even, false_and, ite_false]
      rw [Slice.getElem!_Nat_eq, windowExact, zeroValues]
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_replicate,
        show i < zeros.length by omega, ite_true, Option.getD_some]
  · rw [ite_eq_right inside, List.getElem!_setSlice!_suffix _ _ _ _ (by omega),
      List.getElem!_setSlice!_suffix _ _ _ _ (by omega), ← Slice.getElem!_Nat_eq]

theorem square_into_refines : actualSquareIntoReturnsExactFrame := by
  intro K kernels nativeSquare a dst raw
  by_cases machine : 2 * a.length ≤ Usize.max
  · rw [ite_eq_left machine]
    obtain ⟨size, sizeNormal, sizeProduct⟩ := RawMulTable.normal_of_spec _ _
      (Usize.mul_spec (x := 2#usize) (y := a.len) (by simpa using machine))
    have sizeValue : size.val = 2 * a.length := by simpa using sizeProduct
    by_cases valid : 2 * a.length ≤ dst.length ∧ 2 * a.length ≤ raw.length
    · rw [ite_eq_left valid]
      have dstGuard : size ≤ dst.len := by rw [UScalar.le_equiv, Slice.len_val, sizeValue]; exact valid.1
      have rawGuard : size ≤ raw.len := by rw [UScalar.le_equiv, Slice.len_val, sizeValue]; exact valid.2
      have dstBound : size.val ≤ dst.length := by omega
      obtain ⟨⟨clearWindow, writeBack⟩, prefixNormal, _, prefixLength, writeBackExact⟩ :=
        RawMulTable.normal_of_spec _ _
          (core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec { «end» := size } dst dstBound)
      obtain ⟨zeros, fillNormal, zerosLength, zerosValues⟩ := RawMulTable.normal_of_spec _ _
        (core.slice.Slice.fill.spec core.clone.CloneU64 clearWindow 0#u64
          (by exact (WP.spec_ok (0#u64)).mpr rfl))
      let filled := writeBack zeros
      have filledValues : filled.val = dst.val.setSlice! 0 zeros.val := writeBackExact zeros
      have filledLength : filled.length = dst.length := by
        change filled.val.length = dst.val.length
        simp [filledValues]
      have filledBound : size.val ≤ filled.length := by rw [filledLength]; exact dstBound
      obtain ⟨⟨window, restore⟩, windowNormal, windowValues, windowLength, restoreExact⟩ :=
        RawMulTable.normal_of_spec _ _
          (core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec { «end» := size } filled filledBound)
      change window.length = size.val at windowLength
      change clearWindow.length = size.val at prefixLength
      have shape : window.length = 2 * a.length := by omega
      have scanned := square_loop_refines kernels nativeSquare window a shape 0 (Nat.zero_le _) (fun state => state)
      let output := restore (squareFrom window a 0)
      have outputValues : output.val =
          (dst.val.setSlice! 0 zeros.val).setSlice! 0 (squareFrom window a 0).val := by
        change (restore (squareFrom window a 0)).val = _
        rw [restoreExact, filledValues]
      obtain ⟨outputLength, frame⟩ := restored_frame a dst zeros window output
        (by omega) (by simpa [zerosLength] using zerosValues) valid.1
        (by rw [windowValues, List.slice_zero_j, filledValues, sizeValue]) outputValues
      have outputBound : size.val ≤ output.length := by rw [outputLength]; exact dstBound
      obtain ⟨activePrefix, activeNormal, activeValues, _⟩ := RawMulTable.normal_of_spec _ _
        (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec { «end» := size } output outputBound)
      obtain ⟨normalized, normalizeNormal, normalizedValue⟩ := DenseNormalization.normalized_len_refines activePrefix
      refine ⟨normalized, output, ?_, outputLength, frame, ?_⟩
      · have filledExact : writeBack zeros = filled := rfl
        simp only [square_into, sizeNormal, massert, dstGuard, rawGuard, ite_true, bind_ok,
          Slice.index_mut_SliceIndexRangeToUsizeSliceInst, prefixNormal]
        dsimp! only
        simp only [fillNormal, bind_ok, filledExact, windowNormal]
        dsimp! only
        simp only [core.slice.Slice.iter_mut, bind_ok, DenseSquareRuntime.stepBy,
          show (2#usize).val ≠ 0 by simp, ite_false]
        dsimp! only
        simp only [DenseSquareRuntime.zip,
          SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
        dsimp! only
        change (do
          let back ← square_into_loop bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
            kernels (stateAt window a 0) (fun state => state)
          let active ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U64)
            (restore back.fst.iter.slice) { «end» := size }
          let normalized ← bulksketch.poly.dense.normalized_len active
          Result.ok (normalized, restore back.fst.iter.slice, raw)) = _
        rw [scanned]
        simp only [Bind.bind, bind_ok]
        change (do
          let active ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U64)
            output { «end» := size }
          let normalized ← bulksketch.poly.dense.normalized_len active
          Result.ok (normalized, output, raw)) = _
        simp only [Slice.index_SliceIndexRangeToUsizeSliceInst, activeNormal,
          normalizeNormal, Bind.bind, bind_ok]
      · rw [normalizedValue, activeValues, List.slice_zero_j, sizeValue]
    · rw [ite_eq_right valid]
      by_cases dstEnough : 2 * a.length ≤ dst.length
      · have dstGuard : size ≤ dst.len := by rw [UScalar.le_equiv, Slice.len_val, sizeValue]; exact dstEnough
        have rawReject : ¬ size ≤ raw.len := by
          rw [UScalar.le_equiv, Slice.len_val, sizeValue]
          exact fun rawEnough => valid ⟨dstEnough, rawEnough⟩
        simp only [square_into, sizeNormal, massert, dstGuard, rawReject, ite_true, ite_false, bind_ok, bind_fail]
      · have dstReject : ¬ size ≤ dst.len := by rw [UScalar.le_equiv, Slice.len_val, sizeValue]; exact dstEnough
        simp only [square_into, sizeNormal, massert, dstReject, ite_false, bind_ok, bind_fail]
  · rw [ite_eq_right machine]
    have overflow : (2#usize) * a.len = Result.fail Error.integerOverflow := by
      change UScalar.mul (2#usize) a.len = _
      unfold UScalar.mul UScalar.tryMk UScalar.tryMkOpt
      have tooLarge : ¬ UScalar.check_bounds .Usize ((2#usize).val * a.len.val) := by
        intro bounded
        have inBounds := UScalar.check_bounds_imp_inBounds bounded
        change (2#usize).val * a.len.val < 2 ^ UScalarTy.Usize.numBits at inBounds
        simp only [show (2#usize).val = 2 by simp, Slice.len_val] at inBounds
        apply machine
        rw [Usize.max, Usize.numBits]
        omega
      rw [dite_eq_right tooLarge]
      rfl
    simp only [square_into, overflow, bind_fail]

end BulksketchBridge.DenseSquare
