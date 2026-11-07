import BulksketchBridge.DenseCoefficientSpec
import BulksketchBridge.DenseNormalization

namespace BulksketchBridge.DenseCoefficient

open Aeneas Aeneas.Std

/-- The generated source method handles both guards, clears the exact growth
window, updates one coefficient, and normalizes the resulting active prefix. -/
theorem xor_coefficient_refines : XorCoefficientRefines := by
  intro F K field backend original length index value
  dsimp only
  by_cases valid : length.val ≤ original.length ∧ index.val < original.length
  · rw [ite_eq_left valid]
    have lengthGuard : length ≤ Slice.len original := by scalar_tac
    have indexGuard : index < Slice.len original := by scalar_tac
    have canAdvance : index.val + (1#usize).val ≤ Usize.max := by
      have capacity := original.length_ineq
      change original.length ≤ Usize.max at capacity
      simp only [show (1#usize).val = 1 by simp]
      omega
    obtain ⟨next, addNormal, nextValue⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := index) (y := 1#usize) canAdvance)
    let size := core.cmp.impls.OrdUsize.max length next
    have sizeValue : size.val = activeSize length.val index.val := by
      simp only [size, core.cmp.impls.OrdUsize.max_val, nextValue,
        show (1#usize).val = 1 by simp, activeSize]
    have sizeBound : size.val ≤ original.length := by
      rw [sizeValue]
      exact max_le valid.1 (by omega)
    have windowOrdered : length ≤ size := by
      apply (UScalar.le_equiv _ _).mpr
      rw [sizeValue]
      exact Nat.le_max_left _ _
    obtain ⟨⟨window, writeBack⟩, windowNormal, _, windowLength, writeBackExact⟩ :=
      RawMulTable.normal_of_spec _ _ (core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec
        { start := length, «end» := size } original windowOrdered sizeBound)
    obtain ⟨zeros, fillNormal, _, zerosValues⟩ := RawMulTable.normal_of_spec _ _
      (core.slice.Slice.fill.spec core.clone.CloneU64 window 0#u64
        (by exact (WP.spec_ok (0#u64)).mpr rfl))
    let filled := writeBack zeros
    have cleared : filled = original.setSlice! length.val
        (List.replicate (activeSize length.val index.val - length.val) 0#u64) := by
      change writeBack zeros = _
      rw [writeBackExact zeros]
      change original.setSlice! length.val zeros.val = _
      rw [zerosValues, windowLength, sizeValue]
    have filledLength : filled.length = original.length := by
      rw [cleared, Slice.setSlice!_length]
    have readBound : index.val < filled.length := filledLength ▸ valid.2
    obtain ⟨current, readNormal, currentValue⟩ := RawMulTable.normal_of_spec _ _
      (Slice.index_usize_spec filled index readBound)
    have readExact : current = filled[index.val]! := by
      rw [currentValue, Slice.getElem!_Nat_eq]
      exact List.Inhabited_getElem_eq_getElem! _ _ readBound
    obtain ⟨result, updateNormal, updated⟩ := RawMulTable.normal_of_spec _ _
      (Slice.update_spec filled index (current ^^^ value) readBound)
    obtain ⟨resultLength, frame⟩ :=
      coefficient_frame original filled result length index value current valid.2 cleared readExact updated
    have prefixBound : size.val ≤ result.length := resultLength ▸ sizeBound
    obtain ⟨activePrefix, prefixNormal, prefixValues, _⟩ := RawMulTable.normal_of_spec _ _
      (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
        { «end» := size } result prefixBound)
    obtain ⟨normalized, normalizeNormal, normalizedValue⟩ :=
      DenseNormalization.normalized_len_refines activePrefix
    refine ⟨normalized, result, ?_, resultLength, frame, ?_⟩
    · have sizeExact : core.cmp.impls.OrdUsize.max length next = size := rfl
      have filledExact : writeBack zeros = filled := rfl
      simp only [bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.xor_coefficient,
        massert, lengthGuard, indexGuard, ite_true, bind_ok, addNormal, lift, sizeExact,
        Slice.index_mut_SliceIndexRangeUsizeSliceInst, windowNormal]
      dsimp! only
      simp only [fillNormal, bind_ok, filledExact, readNormal, updateNormal,
        Slice.index_SliceIndexRangeToUsizeSliceInst, prefixNormal, normalizeNormal]
    · rw [normalizedValue, prefixValues, List.slice_zero_j, sizeValue]
  · rw [ite_eq_right valid]
    by_cases lengthValid : length.val ≤ original.length
    · have lengthGuard : length ≤ Slice.len original := by scalar_tac
      have indexGuard : ¬index < Slice.len original := by
        rw [UScalar.lt_equiv, Slice.len_val]
        exact fun indexValid => valid ⟨lengthValid, indexValid⟩
      simp only [bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.xor_coefficient,
        massert, lengthGuard, indexGuard, ite_true, ite_false, bind_ok, bind_fail]
    · have lengthGuard : ¬length ≤ Slice.len original := by scalar_tac
      simp only [bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.xor_coefficient,
        massert, lengthGuard, ite_false, bind_fail]

end BulksketchBridge.DenseCoefficient
