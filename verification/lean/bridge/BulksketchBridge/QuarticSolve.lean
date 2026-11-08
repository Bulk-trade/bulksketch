import BulksketchBridge.QuarticSolveSpec
import BulksketchBridge.QuarticSemantics
import BulksketchBridge.RebuiltLocatorLoop

namespace BulksketchBridge.QuarticSolve

open Aeneas Aeneas.Std Aeneas.Std.WP DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.deg34

private theorem read_slice (words : Slice U64) (index : Usize) (bound : index.val < words.length) :
    Slice.index_usize words index = Result.ok words[index.val]! := by
  obtain ⟨word, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bound)
  rw [normal, exactWord, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bound)

private theorem read_array {size : Usize} (words : Array U64 size) (index : Usize) (bound : index.val < size.val) :
    Array.index_usize words index = Result.ok words[index.val]! := by
  have bounded : index.val < words.length := by simpa using bound
  obtain ⟨word, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _ (Array.index_usize_spec words index bounded)
  rw [normal, exactWord, Array.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bounded)

private theorem degree_normal (factor : Slice U64) (degree : Usize) (shape : factor.length = degree.val + 1) :
    (factor.len - 1#usize : Result Usize) = Result.ok degree := by
  obtain ⟨value, normal, exactValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := factor.len) (y := 1#usize) (by rw [Slice.len_val]; change 1 ≤ factor.length; omega))
  have equal : value = degree := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val] at exactValue
    change value.val = factor.length - 1 at exactValue
    omega
  rw [normal, equal]

private theorem array_prefix {size : Usize} (words : Array U64 size) (stop : Usize)
    (bound : stop.val ≤ size.val) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U64))
      words ⟨stop⟩ = Result.ok (prefixSlice words.to_slice stop.val) := by
  exact shared_prefix_normal words.to_slice stop (by simpa [Array.to_slice] using bound)

private theorem copy_prefix {size : Usize} (output : Slice U64) (words : Array U64 size)
    (room : size.val ≤ output.length) :
    core.slice.Slice.copy_from_slice core.marker.CopyU64
      (prefixSlice output size.val) words.to_slice = Result.ok words.to_slice := by
  have same : (prefixSlice output size.val).length = words.to_slice.length := by
    simp [Nat.min_eq_left room, Array.to_slice]
  obtain ⟨updated, normal, equal⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.Slice.copy_from_slice.step_spec core.marker.CopyU64 _ _ same)
  rw [normal, equal]

private theorem array_full {size : Usize} (words : Array U64 size) :
    prefixSlice words.to_slice size.val = words.to_slice := by
  rw [Slice.eq_iff]
  simp only [prefixSlice, Slice.from_val]
  have length : words.to_slice.val.length = size.val := by simp [Array.to_slice]
  rw [← length, List.take_length]

private def padCubic (words : Array U64 3#usize) : Array U64 4#usize :=
  Array.make 4#usize [words[0]!, words[1]!, words[2]!, 0#u64]

private theorem cubic_prefix (words : Array U64 3#usize) :
    prefixSlice (padCubic words).to_slice 3 = words.to_slice := by
  rw [Slice.eq_iff]
  simp only [prefixSlice, Slice.from_val, Array.to_slice, padCubic, Array.make, Array.from_val]
  change [words[0]!, words[1]!, words[2]!] = words.val
  apply List.ext_getElem (by simp)
  intro index leftBound rightBound
  have bound : index < 3 := by simpa using leftBound
  interval_cases index <;> simp only [Array.getElem!_Nat_eq, List.getElem_cons_zero, List.getElem_cons_succ] <;>
    exact (List.Inhabited_getElem_eq_getElem! _ _ rightBound).symm

private theorem bits_normal : bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = 64#u32 := by
  unfold bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS
  rfl

/-- The native cubic branch copies exactly the three returned words and restores the output tail. -/
theorem solve_cubic_refines : ActualSolveCubicFrame := by
  intro K kernels factor output candidates shape room call
  have degree := degree_normal factor 3#usize (by simpa using shape)
  have bound (index : Usize) (small : index.val < 4) : index.val < factor.length := by omega
  have cRead : Slice.index_usize factor 2#usize = Result.ok factor[2]! := read_slice factor 2#usize (bound _ (by decide))
  have bRead : Slice.index_usize factor 1#usize = Result.ok factor[1]! := read_slice factor 1#usize (bound _ (by decide))
  have aRead : Slice.index_usize factor 0#usize = Result.ok factor[0]! := read_slice factor 0#usize (bound _ (by decide))
  cases candidates with
  | none =>
    simp only [solve, bits_normal, bind_ok, massert, degree, ite_true, cRead, bRead, aRead, call,
      bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual, expectedFrame]
  | some roots =>
    have write := prefix_normal output 3#usize room
    have source := array_prefix (padCubic roots) 3#usize (by decide)
    change _ = Result.ok (prefixSlice (padCubic roots).to_slice 3) at source
    rw [cubic_prefix roots] at source
    simp only [solve, bits_normal, bind_ok, massert, degree, ite_true, cRead, bRead, aRead, call,
      bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch, read_array roots 0#usize (by decide),
      read_array roots 1#usize (by decide), read_array roots 2#usize (by decide),
      Slice.index_mut_SliceIndexRangeToUsizeSliceInst, write]
    dsimp! only
    change (do
      let src ← core.array.Array.index
        (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U64)) (padCubic roots) ⟨3#usize⟩
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU64 (prefixSlice output 3) src
      Result.ok (some 3#usize, restorePrefix output copied)) = _
    have copy : core.slice.Slice.copy_from_slice core.marker.CopyU64 (prefixSlice output 3) roots.to_slice =
        Result.ok roots.to_slice := copy_prefix output roots room
    simp only [Bind.bind, source, bind_ok, copy]

/-- The native quartic branch copies exactly the four returned words and restores the output tail. -/
theorem solve_quartic_refines : ActualSolveQuarticFrame := by
  intro K kernels factor output candidates shape room call
  have degree := degree_normal factor 4#usize (by simpa using shape)
  have unequal : (4#usize : Usize) ≠ 3#usize := by decide
  cases candidates with
  | none =>
    simp only [solve, bits_normal, bind_ok, massert, degree, unequal, ite_true, ite_false, call,
      bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual, expectedFrame]
  | some roots =>
    have write := prefix_normal output 4#usize room
    have source := array_prefix roots 4#usize (by decide)
    rw [array_full roots] at source
    simp only [solve, bits_normal, bind_ok, massert, degree, unequal, ite_true, ite_false, call,
      bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      Slice.index_mut_SliceIndexRangeToUsizeSliceInst, write]
    dsimp! only
    simp only [source, bind_ok, copy_prefix output roots room]

theorem solve_candidate_frames : ActualSolveCandidateFrames :=
  ⟨solve_cubic_refines, solve_quartic_refines⟩

theorem solve_refines : ActualSolveReturnsExactFrame := by
  intro K kernels factor output arithmetic degree room
  rcases degree with cubicLength | quarticLength
  · obtain ⟨candidates, normal, _⟩ :=
      Cubic.cubic_refines kernels factor[2]! factor[1]! factor[0]! arithmetic
    exact ⟨expectedFrame output candidates,
      solve_cubic_refines kernels factor output candidates cubicLength (by omega) normal,
      fun _ => ⟨candidates, normal, rfl⟩, by omega⟩
  · obtain ⟨candidates, normal, _⟩ := QuarticSemantics.quartic_refines kernels factor arithmetic (by omega)
    exact ⟨expectedFrame output candidates,
      solve_quartic_refines kernels factor output candidates quarticLength (by omega) normal,
      by omega, fun _ => ⟨candidates, normal, rfl⟩⟩

end BulksketchBridge.QuarticSolve
