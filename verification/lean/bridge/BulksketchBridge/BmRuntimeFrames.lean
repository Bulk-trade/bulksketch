import BulksketchBridge.BmRuntimeFramesSpec

namespace BulksketchBridge.BmRuntimeFrames

open Aeneas Aeneas.Std

private theorem exclusive_normal (words : Slice U64) (range : InclusiveRange)
    (bound : range.end.val < words.length) :
    ∃ bounds : core.ops.range.Range Usize,
      BmLocatorRuntime.exclusiveRange range = Result.ok bounds ∧
      bounds.start.val = startIndex range ∧ bounds.end.val = range.end.val + 1 := by
  have sizeBound : words.length ≤ Usize.max := words.length_ineq
  obtain ⟨stop, normal, value⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := range.end) (y := 1#usize) (by
      change range.end.val + 1 ≤ Usize.max
      omega))
  have stopValue : stop.val = range.end.val + 1 := value
  refine ⟨⟨if range.exhausted then stop else range.start, stop⟩, ?_, ?_, stopValue⟩
  · simp only [BmLocatorRuntime.exclusiveRange, normal, bind_ok]
  · cases exhausted : range.exhausted <;> simp [startIndex, exhausted, stopValue]

theorem inclusive_shared_normal : InclusiveSharedRefines := by
  intro words range admitted
  obtain ⟨bounds, normal, first, last⟩ := exclusive_normal words range admitted.1
  have indexNormal := ClosedLeaf.shared_region_normal words bounds.start bounds.end
    (by rw [first, last]; exact admitted.2) (by rw [last]; exact Nat.succ_le_of_lt admitted.1)
  simpa only [BmLocatorRuntime.inclusiveRange, admitted.1, ite_true, normal, bind_ok, first, last]
    using indexNormal

theorem inclusive_mutable_normal : InclusiveMutableRefines := by
  intro words range admitted
  obtain ⟨bounds, normal, first, last⟩ := exclusive_normal words range admitted.1
  have indexNormal := ClosedLeaf.mutable_region_normal words bounds.start bounds.end
    (by rw [first, last]; exact admitted.2) (by rw [last]; exact Nat.succ_le_of_lt admitted.1)
  simpa only [BmLocatorRuntime.inclusiveRange, admitted.1, ite_true, normal, bind_ok, first, last]
    using indexNormal

theorem inclusive_shared_new (words : Slice U64) (start last : Usize)
    (ordered : start.val ≤ last.val + 1) (bounded : last.val < words.length) :
    (BmLocatorRuntime.inclusiveRange U64).index ⟨start, last, false⟩ words =
      Result.ok (ClosedLeaf.region words start.val (last.val + 1)) :=
  inclusive_shared_normal words ⟨start, last, false⟩ ⟨bounded, ordered⟩

theorem inclusive_mutable_new (words : Slice U64) (start last : Usize)
    (ordered : start.val ≤ last.val + 1) (bounded : last.val < words.length) :
    (BmLocatorRuntime.inclusiveRange U64).index_mut ⟨start, last, false⟩ words =
      Result.ok (ClosedLeaf.region words start.val (last.val + 1),
        fun replacement => words.setSlice! start.val replacement.val) :=
  inclusive_mutable_normal words ⟨start, last, false⟩ ⟨bounded, ordered⟩

theorem writeback_frame (words : Slice U64) (start stop : Nat) (ordered : start ≤ stop) :
    BackwardFrame words start stop (fun replacement => words.setSlice! start replacement.val) := by
  intro replacement length
  refine ⟨Slice.setSlice!_length _ _ _, ?_⟩
  intro index bound
  have inside : index < words.val.length := bound
  have replacementLength : replacement.val.length = stop - start := length
  simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
  split
  · rename_i active
    exact List.getElem!_setSlice!_middle _ _ _ _ ⟨active.1, by omega, inside⟩
  · rename_i outside
    exact List.getElem!_setSlice!_same _ _ _ _ (by omega)

theorem inclusive_writeback_frame : InclusiveWritebackRefines := by
  intro words range admitted
  exact ⟨_, _, inclusive_mutable_normal words range admitted, rfl,
    writeback_frame words (startIndex range) (range.end.val + 1) admitted.2⟩

theorem zip_iterator_normal : ZipIteratorRefines := by
  intro A B left right
  simp only [Aeneas.Std.MutableZip.construct,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok]

theorem zip_shared_slice_normal : ZipSharedSliceRefines := by
  intro A B left right
  simp only [Aeneas.Std.MutableZip.construct,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]

end BulksketchBridge.BmRuntimeFrames
