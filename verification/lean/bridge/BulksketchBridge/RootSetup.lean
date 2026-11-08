import BulksketchBridge.RootSetupSpec
import BulksketchBridge.BmEntry
import BulksketchBridge.ClosedLeafAdvance
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.RootSetup

open Aeneas Aeneas.Std DenseCoefficient BmEntry RebuiltLfsr
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

theorem factor_work_refines : ActualFactorWork := by
  intro degree polynomials table raw basis polyBound tableBound
  have polyMax := Slice.length_ineq polynomials
  change polynomials.length ≤ Usize.max at polyMax
  have tableMax := Slice.length_ineq table
  change table.length ≤ Usize.max at tableMax
  obtain ⟨width, widthNormal, widthValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := degree) (y := 1#usize)
      (by change degree.val + 1 ≤ Usize.max; omega))
  change width.val = degree.val + 1 at widthValue
  obtain ⟨half, halfNormal, halfValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.div_spec degree (y := 2#usize) (by simp))
  change half.val = degree.val / 2 at halfValue
  have mulFits : degree.val * half.val ≤ Usize.max := by
    rw [halfValue]
    exact tableBound.trans tableMax
  obtain ⟨count, mulNormal, countValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := degree) (y := half) mulFits)
  change count.val = degree.val * half.val at countValue
  rw [halfValue, ← tableCount] at countValue
  let afterModulus := tail polynomials width.val
  let afterTrace := tail afterModulus degree.val
  have afterModulusLength : afterModulus.length = polynomials.length - width.val :=
    tail_length _ _
  have afterTraceLength : afterTrace.length = polynomials.length - width.val - degree.val := by
    change (tail afterModulus degree.val).length = _
    rw [tail_length, afterModulusLength]
  have splitModulus := split_refines polynomials width (by omega)
  have splitTrace := split_refines afterModulus degree (by omega)
  have splitGcd := split_refines afterTrace width (by omega)
  have splitTable := prefix_normal table count (by omega)
  simp only [FactorWork.new, widthNormal, splitModulus, bind_ok]
  dsimp! only
  rw [splitTrace]
  simp only [bind_ok]
  dsimp! only
  rw [splitGcd]
  simp only [bind_ok]
  dsimp! only
  simp only [halfNormal, mulNormal, Slice.index_mut_SliceIndexRangeToUsizeSliceInst,
    splitTable, bind_ok, countValue]
  dsimp! only [afterTrace, afterModulus, workRegions, restoreWork]
  rw [widthValue]
  rfl

theorem root_configuration_refines : ActualRootConfiguration :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem root_start_refines : ActualRootStart := by
  intro roots degree workspace bounds
  obtain ⟨width, widthNormal, widthValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := degree) (y := 1#usize) bounds.1)
  have widthExact : width = ClosedLeafAdvance.usizeWord (degree.val + 1) := by
    apply Usize.bv_eq_imp_eq
    change width.bv = BitVec.ofNat System.Platform.numBits (degree.val + 1)
    change width.val = degree.val + 1 at widthValue
    rw [← widthValue, Usize.BitVec_ofNat_val]
  simp only [Roots.start, widthNormal, bind_ok, gf64Dictionary]
  congr 1
  funext preferred
  have stage (r : Roots) := ClosedLeafAdvance.stage_refines r
  by_cases zero : degree = 0#usize
  · simp only [zero, bne_self_eq_false, Bool.false_eq_true, ite_false, bind_ok,
      startedWorkspace, startedRoots, ite_true, stage] at *
    simp only [widthExact]
    rfl
  · have test : (degree != 0#usize) = true := by simp [zero]
    obtain ⟨polyBound, bmBound⟩ := bounds.2 zero
    have poly := inclusive_prefix workspace.polynomials degree polyBound
    have bm := ClosedLeaf.inclusive_prefix_normal workspace.bm degree bmBound
    have polyLen : (prefixSlice workspace.polynomials (degree.val + 1)).length = degree.val + 1 :=
      (prefix_length _ _).trans (Nat.min_eq_left (by omega))
    have bmLen : (prefixSlice workspace.bm (degree.val + 1)).length = degree.val + 1 :=
      (prefix_length _ _).trans (Nat.min_eq_left (by omega))
    have copy := ClosedLeaf.copy_normal (prefixSlice workspace.polynomials (degree.val + 1))
      (prefixSlice workspace.bm (degree.val + 1)) (polyLen.trans bmLen.symm)
    simp only [test, ite_true, core.slice.index.Slice.index_mut, core.slice.index.Slice.index,
      poly, bm, bind_ok, stage, startedRoots, startedWorkspace, zero, ite_false]
    dsimp! only
    simp only [copy, bind_ok, widthExact]
    rfl

end BulksketchBridge.RootSetup
