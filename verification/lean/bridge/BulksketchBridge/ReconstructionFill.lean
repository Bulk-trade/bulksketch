import BulksketchBridge.ReconstructionLoop

namespace BulksketchBridge.Reconstruction

open Aeneas Aeneas.Std Aeneas.Std.WP
open bulksketch.decode.stages.Execution

theorem fill_normal {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : bulksketch.backend.contract.BulkKernels K F) (difference initial : Slice U64)
    (square : ∀ word, kernels.ArithmeticInst.square word = .ok (squareWord word))
    (room : 2 * difference.length < initial.length) :
    ∃ endpoint range final,
      Slice.update initial 0#usize 0#u64 = .ok (initial.setAtNat 0 0#u64) ∧
      (2#usize * Slice.len difference : Result Usize) = Result.ok endpoint ∧
      core.ops.range.RangeInclusive.new 1#usize endpoint = .ok range ∧
      reconstruct_loop0 field kernels range difference (initial.setAtNat 0 0#u64) = .ok final ∧
      reconstruct_loop1 field kernels range difference (initial.setAtNat 0 0#u64) = .ok final ∧
      Prefix difference initial final (2 * difference.length + 1) := by
  have fits := Slice.length_ineq initial
  change initial.length ≤ Usize.max at fits
  have safe : (2#usize).val * (Slice.len difference).val ≤ Usize.max := by
    rw [Slice.len_val]
    change 2 * difference.length ≤ Usize.max
    omega
  obtain ⟨endpoint, multiply, endEq⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := 2#usize) (y := Slice.len difference) safe)
  have endValue : endpoint.val = 2 * difference.length := by simpa using endEq
  let range : Inclusive := ⟨1#usize, endpoint, false⟩
  have newRange : core.ops.range.RangeInclusive.new 1#usize endpoint = .ok range := rfl
  have inv : Prefix difference initial (initial.setAtNat 0 0#u64) (processed range) :=
    initial_prefix _ _ (by omega)
  obtain ⟨final, loop0, result⟩ := reconstruct_loop0_refines field kernels range difference initial _
    square (by simp [range]) (by simp [range]) endValue (by change endpoint.val < initial.length; omega) inv
  exact ⟨endpoint, range, final, update_normal initial 0#usize 0#u64 (by change 0 < initial.length; omega),
    multiply, newRange, loop0, loop0, result⟩

end BulksketchBridge.Reconstruction
