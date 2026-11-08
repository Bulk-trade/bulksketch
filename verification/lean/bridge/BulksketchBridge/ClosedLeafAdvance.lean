import BulksketchBridge.ClosedLeafAdvanceSpec
import BulksketchBridge.StageCharge
import BulksketchBridge.CertificateLoop

namespace BulksketchBridge.ClosedLeafAdvance

open Aeneas Aeneas.Std Aeneas.Std.WP
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.decode.work bulksketch.types
open DenseCoefficient

theorem stage_refines : ActualStageRefines := by
  intro roots
  by_cases small : roots.degree < 3#usize <;>
    cases closed : roots.closed_form <;>
    by_cases three : roots.degree = 3#usize <;> by_cases four : roots.degree = 4#usize <;>
    simp [Roots.stage, stageFor, small, closed, three, four]

theorem charge_refines : ActualRootsChargeRefines := by
  intro meter operation
  unfold charge
  congr 1
  funext cost
  cases cost with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, StageCharge.chargeResult]
  | Ok amount =>
    obtain ⟨final, charged, state⟩ := WorkMeter.charge_refines meter amount
    have exactState : final = StageCharge.meterOfModel
        ((WorkMeter.toModel meter).charge (WorkMeter.toUInt64 amount)).1 := by
      apply WorkMeter.toModel_injective
      rw [StageCharge.toModel_meterOfModel]
      exact state
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, StageCharge.chargeResult]
    rw [charged, exactState]

theorem advance_empty_refines (roots : Roots) (workspace : RowWorkspace)
    (empty : roots.pending = 0#usize) :
    Roots.advance roots workspace = Result.ok (.Verification, roots, workspace, id) := by
  simp only [Roots.advance, empty, ite_true]
  rfl

private theorem word_eq (word : Usize) (value : Nat) (exactValue : word.val = value) :
    word = usizeWord value := by
  apply Usize.bv_eq_imp_eq
  change word.bv = BitVec.ofNat _ value
  rw [← exactValue, Usize.BitVec_ofNat_val]

private theorem sub_one (word : Usize) (positive : 1 ≤ word.val) :
    (word - 1#usize : Result Usize) = Result.ok (usizeWord (word.val - 1)) := by
  obtain ⟨value, normal, exactValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := word) (y := 1#usize) (by exact positive))
  rw [normal, word_eq value (word.val - 1) exactValue.1]

private theorem add (left right : Usize) (fits : left.val + right.val ≤ Usize.max) :
    (left + right : Result Usize) = Result.ok (usizeWord (left.val + right.val)) := by
  obtain ⟨value, normal, exactValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := left) (y := right) fits)
  rw [normal, word_eq value _ exactValue]

private theorem word_val (value : Nat) (fits : value ≤ Usize.max) :
    (usizeWord value).val = value := by
  rw [← Usize.bv_toNat]
  change (BitVec.ofNat System.Platform.numBits value).toNat = value
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  simp only [Usize.max, Usize.numBits] at fits
  change value < 2 ^ System.Platform.numBits
  change value ≤ 2 ^ System.Platform.numBits - 1 at fits
  have positive : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  omega

private theorem read_frame (stack : Slice FactorFrame) (index : Usize) (frame : FactorFrame)
    (read : stack.val[index.val]? = some frame) :
    Slice.index_usize stack index = Result.ok frame := by
  obtain ⟨bounded, exactFrame⟩ := List.getElem?_eq_some_iff.mp read
  obtain ⟨word, normal, value⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec stack index bounded)
  rw [normal, value]
  exact congrArg Result.ok exactFrame

private theorem read_word (words : Slice U64) (index : Usize) (bounded : index.val < words.length) :
    Slice.index_usize words index = Result.ok words[index.val]! := by
  obtain ⟨word, normal, exactValue⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec words index bounded)
  rw [normal, exactValue, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ bounded)

private theorem convert (word : U64) (fits : word.val ≤ Usize.max) :
    Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from word =
      Result.ok (.Ok (usizeWord word.val)) := by
  obtain ⟨value, normal, exactValue⟩ := checked_unsigned_conversion_normal (target := .Usize) word (by
    simpa only [UScalar.max, Usize.max, Usize.numBits] using fits)
  exact normal.trans (congrArg (fun w => Result.ok (core.result.Result.Ok w)) (word_eq value _ exactValue))

private theorem exact_factor_slice (workspace : RowWorkspace) (frame : FactorFrame)
    (bounds : frame.coefficient_start.val + frame.coefficient_len.val ≤ workspace.factors.length) :
    ∃ words : Slice U64,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U64) workspace.factors
        ⟨usizeWord frame.coefficient_start.val, usizeWord (frame.coefficient_start.val + frame.coefficient_len.val)⟩ =
        Result.ok words ∧
      words.length = frame.coefficient_len.val ∧
      poppedWorkspace workspace frame =
        { workspace with polynomials := RebuiltLfsr.restorePrefix workspace.polynomials words } := by
  have max : workspace.factors.length ≤ Usize.max := workspace.factors.length_ineq
  have start := word_val frame.coefficient_start.val (by omega)
  have stop := word_val (frame.coefficient_start.val + frame.coefficient_len.val) (by omega)
  rw [Slice.index_SliceIndexRangeUsizeSliceInst]
  obtain ⟨words, normal, exactWords, length⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      ⟨usizeWord frame.coefficient_start.val, usizeWord (frame.coefficient_start.val + frame.coefficient_len.val)⟩
      workspace.factors (by rw [UScalar.le_equiv]; dsimp only; omega) (by dsimp only; omega))
  refine ⟨words, normal, by dsimp only at length; omega, ?_⟩
  dsimp only [poppedWorkspace]
  congr 2
  rw [Slice.eq_iff, exactWords]
  simp only [Slice.from_val, List.slice, start, stop, Nat.add_sub_cancel_left]

/-- The pending frame is popped and its coefficients, degree and direction
are restored before dispatching the next traversal stage. -/
theorem advance_pop_refines (roots : Roots) (workspace : RowWorkspace) (frame : FactorFrame)
    (bounds : PopBounds roots workspace frame) :
    let updatedRoots := poppedRoots roots workspace frame
    Roots.advance roots workspace =
      Result.ok (stageFor updatedRoots, updatedRoots, poppedWorkspace workspace frame, id) := by
  obtain ⟨nonzero, frameAt, lenPositive, lenFits, sourceFits, affineFits⟩ := bounds
  have pendingPositive : 1 ≤ roots.pending.val := by
    by_contra bad
    apply nonzero
    have zero : roots.pending.val = 0 := by omega
    exact word_eq roots.pending 0 zero
  have pendingFits : roots.pending.val ≤ Usize.max := by scalar_tac
  have max : workspace.factors.length ≤ Usize.max := workspace.factors.length_ineq
  have index : (usizeWord (roots.pending.val - 1)).val = roots.pending.val - 1 := word_val _ (by omega)
  have readFrame := read_frame workspace.stack (usizeWord (roots.pending.val - 1)) frame (by rwa [index])
  have start : (usizeWord frame.coefficient_start.val).val = frame.coefficient_start.val := word_val _ (by omega)
  have len : (usizeWord frame.coefficient_len.val).val = frame.coefficient_len.val := word_val _ (by omega)
  have addStop : (usizeWord frame.coefficient_start.val + usizeWord frame.coefficient_len.val : Result Usize) =
      Result.ok (usizeWord (frame.coefficient_start.val + frame.coefficient_len.val)) := by
    simpa only [start, len] using add (usizeWord frame.coefficient_start.val)
      (usizeWord frame.coefficient_len.val) (by omega)
  have nextDegree : (usizeWord frame.coefficient_len.val - 1#usize : Result Usize) =
      Result.ok (usizeWord (frame.coefficient_len.val - 1)) := by
    simpa only [len] using sub_one (usizeWord frame.coefficient_len.val) (by omega)
  obtain ⟨words, readWords, wordCount, workspaceEq⟩ := exact_factor_slice workspace frame sourceFits
  obtain ⟨⟨destination, back⟩, prefixNormal, _, prefixLen, writeBack⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec
      ⟨usizeWord frame.coefficient_len.val⟩ workspace.polynomials (by simpa only [len] using lenFits))
  have sameLength : destination.length = words.length := by rw [prefixLen, len, wordCount]
  obtain ⟨copied, copyNormal, copyEq⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.Slice.copy_from_slice.step_spec core.marker.CopyU64 destination words sameLength)
  rw [copyEq] at copyNormal
  have backEq : back words = RebuiltLfsr.restorePrefix workspace.polynomials words := by
    simp only [Slice.eq_iff, writeBack words, RebuiltLfsr.restorePrefix, Slice.from_val]
  simp only [Roots.advance, nonzero, ite_false, sub_one _ pendingPositive, readFrame, bind_ok,
    convert _ (by omega : frame.coefficient_start.val ≤ Usize.max),
    convert _ (by omega : frame.coefficient_len.val ≤ Usize.max), core.result.Result.expect,
    Slice.index_mut_SliceIndexRangeToUsizeSliceInst, prefixNormal, addStop, readWords,
    nextDegree]
  dsimp! only
  simp only [copyNormal, bind_ok, backEq]
  rw [workspaceEq]
  have stageNormal (r : Roots) : Roots.stage r = Result.ok (stageFor r) := stage_refines r
  cases affine : roots.affine
  · simp only [affine, Bool.false_eq_true, ite_false, bind_ok, poppedRoots]
    dsimp! only
    simp only [stageNormal, bind_ok]
    rfl
  · obtain ⟨positive, bounded⟩ := affineFits affine
    have sum := word_val (frame.coefficient_start.val + roots.stride.val) (by omega)
    have addBase : (usizeWord frame.coefficient_start.val + roots.stride : Result Usize) =
        Result.ok (usizeWord (frame.coefficient_start.val + roots.stride.val)) := by
      simpa only [start] using add (usizeWord frame.coefficient_start.val) roots.stride (by omega)
    have baseIndex := word_val (frame.coefficient_start.val + roots.stride.val - 1) (by omega)
    have subBase : (usizeWord (frame.coefficient_start.val + roots.stride.val) - 1#usize : Result Usize) =
        Result.ok (usizeWord (frame.coefficient_start.val + roots.stride.val - 1)) := by
      simpa only [sum] using sub_one (usizeWord (frame.coefficient_start.val + roots.stride.val)) (by omega)
    have readBase := read_word workspace.factors (usizeWord (frame.coefficient_start.val + roots.stride.val - 1))
      (by omega)
    simp only [affine, ite_true, addBase, subBase, readBase, baseIndex, lift, bind_ok, poppedRoots]

    dsimp! only
    simp only [stageNormal, bind_ok]
    rfl

theorem advance_refines : ActualAdvanceRefines := ⟨advance_empty_refines, advance_pop_refines⟩

end BulksketchBridge.ClosedLeafAdvance
