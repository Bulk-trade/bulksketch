import BulksketchBridge.RootLeafSpec
import BulksketchBridge.ClosedLeafAdvance
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.Algebra.WordNative
import BulksketchBridge.InverseUsing
import BulksketchBridge.MapsQuadratic

namespace BulksketchBridge.RootLeaf

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr Algebra.Gf64
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types bulksketch.backend.contract

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem contains_exact (words : Slice U64) :
    core.slice.Slice.contains core.cmp.PartialEqU64 words 0#u64 =
      .ok (decide (0#u64 ∈ words.val)) := by
  unfold core.slice.Slice.contains
  induction words.val with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.anyM_cons, liftFun2, core.cmp.impls.PartialEqU64.eq, ih, List.mem_cons]
    by_cases same : (0#u64 : U64) = head <;> simp [same, pure, Bind.bind]

private theorem array_prefix (words : Array U64 2#usize) (stop : Usize)
    (bound : stop.val ≤ 2) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U64))
      words ⟨stop⟩ = .ok (prefixSlice words.to_slice stop.val) := by
  exact shared_prefix_normal words.to_slice stop (by simpa [Array.to_slice] using bound)

private theorem read_slice (words : Slice U64) (index : Usize) (bound : index.val < words.length) :
    Slice.index_usize words index = .ok words[index.val]! := by
  obtain ⟨word, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec words index bound)
  rw [normal, exactWord, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bound)

private def sourceFinish (roots : Roots) (workspace : RowWorkspace) (words : Slice U64)
    (meter : WorkMeter) : Result LeafFrame := do
  let invalid ← core.slice.Slice.contains core.cmp.PartialEqU64 words 0#u64
  if invalid then .ok (.Ok (.Err .InvalidLocator), roots, workspace, id, meter)
  else
    let count ← roots.count + roots.degree
    let (destination, back) ← core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice U64) workspace.roots ⟨roots.count, count⟩
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU64 destination words
    let (stage, state, final, advanceBack) ← Roots.advance { roots with count }
      { workspace with roots := back copied }
    .ok (.Ok (.Ok stage), state, final, advanceBack, meter)

private theorem finish_refines (roots : Roots) (workspace : RowWorkspace) (words : Slice U64)
    (meter : WorkMeter) (length : words.length = roots.degree.val)
    (room : roots.count.val + roots.degree.val ≤ workspace.roots.length) :
    sourceFinish roots workspace words meter =
      if 0#u64 ∈ words.val then .ok (.Ok (.Err .InvalidLocator), roots, workspace, id, meter)
      else leafResume roots workspace words meter := by
  unfold sourceFinish
  rw [contains_exact]
  by_cases invalid : (0#u64 : U64) ∈ words.val
  · simp [invalid]
  · have size := workspace.roots.length_ineq
    change workspace.roots.length ≤ Usize.max at size
    obtain ⟨count, added, countVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := roots.count) (y := roots.degree) (by omega))
    change count.val = roots.count.val + roots.degree.val at countVal
    have write := ClosedLeaf.mutable_region_normal workspace.roots roots.count count (by omega) (by omega)
    have sameLength : (ClosedLeaf.region workspace.roots roots.count.val count.val).length = words.length := by
      rw [ClosedLeaf.region_length _ _ _ (by omega), countVal, Nat.add_sub_cancel_left, length]
    have copy := ClosedLeaf.copy_normal _ _ sameLength
    have countEq : count = ClosedLeafAdvance.usizeWord (roots.count.val + roots.degree.val) := by
      apply Usize.bv_eq_imp_eq
      change count.bv = BitVec.ofNat System.Platform.numBits (roots.count.val + roots.degree.val)
      rw [← countVal, Usize.BitVec_ofNat_val]
    simp only [invalid, decide_false, bind_ok, Bool.false_eq_true, ite_false, added,
      Slice.index_mut_SliceIndexRangeUsizeSliceInst, write]
    dsimp! only
    rw [copy]
    simp only [bind_ok, leafResume, countEq]

theorem root_leaf_refines : ActualRootLeaf := by
  intro K kernels roots workspace meter arithmetic bounds
  obtain ⟨degreeBound, polyBound, rootBound⟩ := bounds
  rw [Roots.leaf, ClosedLeafAdvance.charge_refines]
  unfold expectedLeaf
  simp only [Aeneas.Std.bind_assoc, bind_ok]
  congr 1
  funext cost
  have mulNormal (a b : U64) : kernels.ArithmeticInst.mul a b =
      .ok (Inverse.multiplyNativeWord a b) :=
    (arithmetic.1 a b).trans (native_mul_word a b)
  have squareNormal (a : U64) : kernels.ArithmeticInst.square a = .ok (Square.expectedWord a) :=
    (arithmetic.2.1 a).trans (Square.square_refines a)
  have quadraticNormal (a : U64) : kernels.ArithmeticInst.solve_quadratic a =
      .ok (MapsQuadratic.expectedSolution a) :=
    (arithmetic.2.2.2 a).trans (MapsQuadratic.solve_quadratic_refines a)
  obtain ⟨paid, finalMeter⟩ := StageCharge.chargeResult meter cost
  cases paid with
  | Err reason =>
    simp [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    rfl
  | Ok paid =>
    cases paid
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    dsimp! only
    have degreeCases : roots.degree.val = 0 ∨ roots.degree.val = 1 ∨ roots.degree.val = 2 := by omega
    rcases degreeCases with zero | one | two
    · have slice := array_prefix (Array.repeat 2#usize 0#u64) roots.degree (by omega)
      rw [zero] at slice
      change _ = Result.ok emptyRoots at slice
      simp only [zero, leafCandidates, slice, bind_ok]
      change sourceFinish roots workspace emptyRoots finalMeter = _
      exact finish_refines roots workspace emptyRoots finalMeter (by simp [emptyRoots, Slice.length, zero]) rootBound
    · have read : Slice.index_usize workspace.polynomials 0#usize = Result.ok workspace.polynomials[0]! :=
        read_slice workspace.polynomials 0#usize (by change 0 < workspace.polynomials.length; omega)
      have slice := array_prefix (Array.make 2#usize [workspace.polynomials[0]!, 0#u64])
        roots.degree (by omega)
      rw [one] at slice
      change _ = Result.ok (oneRoot workspace.polynomials[0]!) at slice
      simp only [one, leafCandidates, read, slice, bind_ok]
      change sourceFinish roots workspace (oneRoot workspace.polynomials[0]!) finalMeter = _
      exact finish_refines roots workspace _ finalMeter (by simp [oneRoot, Slice.length, one]) rootBound
    · let linear := workspace.polynomials[1]!
      have readLinear := read_slice workspace.polynomials 1#usize
        (by change 1 < workspace.polynomials.length; omega)
      have readConstant : Slice.index_usize workspace.polynomials 0#usize = Result.ok workspace.polynomials[0]! :=
        read_slice workspace.polynomials 0#usize (by change 0 < workspace.polynomials.length; omega)
      have readLinearExact : Slice.index_usize workspace.polynomials 1#usize = .ok linear := readLinear
      simp only [two, leafCandidates, readLinearExact, bind_ok]
      by_cases repeated : linear = 0#u64
      · simp [repeated, linear]
        rfl
      · have inverseNormal : kernels.ArithmeticInst.inverse linear =
            .ok (some (DirectTwo.inverseWord linear)) := by
          rw [arithmetic.2.2.1, InverseUsing.inverse_refines]
          simp only [Inverse.expectedFieldInverse, ite_eq_right repeated, DirectTwo.inverseWord]
        have test : workspace.polynomials[1]! ≠ 0#u64 := repeated
        simp only [repeated, test, ite_false, inverseNormal, bind_ok, core.option.Option.expect, Result.ofOption,
          readConstant, squareNormal, mulNormal, quadraticNormal]
        change (match MapsQuadratic.expectedSolution (quadraticTarget workspace.polynomials[0]! linear) with
          | none => _
          | some solution => _) = _
        cases solution : MapsQuadratic.expectedSolution (quadraticTarget workspace.polynomials[0]! linear) with
        | none => rfl
        | some u =>
          let root := Inverse.multiplyNativeWord linear u
          have slice := array_prefix (Array.make 2#usize [root, root ^^^ linear]) roots.degree (by omega)
          rw [two] at slice
          change _ = Result.ok (twoRoots root (root ^^^ linear)) at slice
          simp only [lift, bind_ok]
          rw [slice]
          simp only [bind_ok]
          change sourceFinish roots workspace (twoRoots root (root ^^^ linear)) finalMeter = _
          rw [finish_refines roots workspace _ finalMeter (by simp [twoRoots, Array.to_slice, two]) rootBound]

end BulksketchBridge.RootLeaf
