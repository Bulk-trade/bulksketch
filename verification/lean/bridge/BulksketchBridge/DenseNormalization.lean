import BulksketchBridge.DenseNormalizationSpec
import BulksketchBridge.ReversePosition
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.DenseNormalization

open Aeneas Aeneas.Std

private abbrev predicateCallback :=
  bulksketch.poly.dense.normalized_len.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool

private abbrev indexCallback :=
  bulksketch.poly.dense.normalized_len.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize

private theorem normalized_position (coefficients : List U64) :
    BulksketchBridge.ReversePosition.expected (fun word => word != 0#u64) coefficients.reverse =
      if normalizedLength coefficients = 0 then none else some (normalizedLength coefficients - 1) := by
  unfold BulksketchBridge.ReversePosition.expected normalizedLength
  simp only [bne, Bool.not_not, List.length_reverse]
  generalize (coefficients.reverse.takeWhile (fun word => word == 0#u64)).length = trailing
  by_cases shorter : trailing < coefficients.length
  · simp [shorter, show coefficients.length - trailing ≠ 0 by omega]
  · simp [shorter, show coefficients.length - trailing = 0 by omega]

theorem normalizedLength_le (coefficients : List U64) :
    normalizedLength coefficients ≤ coefficients.length := Nat.sub_le ..

/-- The original generated body returns the exact trailing-zero normalized
length. The original nonzero and index-plus-one callbacks are both executed
through their extracted definitions. -/
theorem normalized_len_refines : NormalizedLenRefines := by
  intro coefficients
  obtain ⟨position, normal, meaning⟩ :=
    BulksketchBridge.ReversePosition.shared_rposition_refines predicateCallback
      (bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT U64)
      (bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT U64)
      ⟨coefficients, 0⟩ () (fun word => word != 0#u64) (by intros; exact ⟨(), rfl⟩)
  simp only [List.drop_zero, normalized_position] at meaning
  have original : bulksketch.poly.dense.normalized_len coefficients =
      core.option.Option.map_or indexCallback position (0#usize) () := by
    simp only [bulksketch.poly.dense.normalized_len, core.slice.Slice.iter, bind_ok, normal]
    rfl
  cases position with
  | none =>
    have zero : normalizedLength coefficients.val = 0 := by
      by_contra nonzero
      simp [nonzero] at meaning
    exact ⟨0#usize, original, by simp [zero]⟩
  | some index =>
    have nonzero : normalizedLength coefficients.val ≠ 0 := by
      intro zero
      simp [zero] at meaning
    have indexValue : index.val = normalizedLength coefficients.val - 1 := by
      simpa only [Option.map_some, nonzero, ite_false, Option.some.injEq] using meaning
    have nextValue : index.val + 1 = normalizedLength coefficients.val := by omega
    have inBounds : index.val + (1#usize).val ≤ Usize.max := by
      rw [show (1#usize).val = 1 by simp, nextValue]
      exact (normalizedLength_le coefficients.val).trans coefficients.length_ineq
    obtain ⟨size, addNormal, addValue⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := index) (y := 1#usize) inBounds)
    refine ⟨size, ?_, ?_⟩
    · rw [original]
      exact addNormal
    · simpa only [show (1#usize).val = 1 by simp, nextValue] using addValue

end BulksketchBridge.DenseNormalization
