import BulksketchBridge.ExecutionVerifySpec
import BulksketchBridge.ProbeVerification
import BulksketchBridge.VerifyDispatch
import BulksketchBridge.StageCharge
import BulksketchBridge.RebuiltLfsr

namespace BulksketchBridge.ExecutionVerify

open Aeneas Aeneas.Std DegreeProbeRuntime DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.work bulksketch.types
open core.result.Result.Insts

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

private theorem rebuilt_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots odd coefficients expected seed : Slice U64) (continued : Bool)
    (admitted : RebuiltAdmission kernels roots odd coefficients expected seed continued) :
    bulksketch.decode.verify.rebuilt_lfsr fieldDictionary kernels roots odd coefficients expected =
      .ok (rebuiltExpected roots odd coefficients expected seed continued) := by
  obtain ⟨result, normal, exactResult⟩ :=
    rebuilt_lfsr_refines kernels admitted.linear admitted.square roots odd coefficients expected seed
      admitted.coefficientsRoom admitted.seedRoom admitted.seedLength admitted.insert
      (fun agrees => ⟨continued, admitted.recurrence agrees⟩)
  rw [normal]
  by_cases agrees : seed = prefixSlice odd seed.length
  · rw [ite_eq_left agrees] at exactResult
    have identical : result = continued :=
      Result.ok_injective (exactResult.symm.trans (admitted.recurrence agrees))
    unfold rebuiltExpected
    rw [ite_eq_left agrees, decide_eq_true_eq.mpr agrees, identical]
    rfl
  · rw [ite_eq_right agrees] at exactResult
    unfold rebuiltExpected
    rw [ite_eq_right agrees, decide_eq_false_iff_not.mpr agrees, exactResult]
    rfl

private theorem dispatch_exact {F K : Type} (self : Execution F K) (input : RowInput) :
    (if self.v3 then
      Aeneas.Std.bind (bulksketch.decode.verify.use_rebuilt_lfsr self.roots.count input.difference.len)
        (fun selected => .ok (self.roots, selected))
      else .ok (self.roots, false)) =
      .ok (self.roots, selects self input) := by
  cases mode : self.v3
  · simp only [selects, mode, Bool.false_and, Bool.false_eq_true, ite_false]
  · simp only [selects, mode, Bool.true_and, ite_true]
    have decision := VerifyDispatch.use_rebuilt_lfsr_refines self.roots.count input.difference.len
    change Aeneas.Std.bind (bulksketch.decode.verify.use_rebuilt_lfsr self.roots.count input.difference.len) _ = _
    rw [decision, bind_ok, Slice.len_val]

private theorem tag_exact {F K : Type} (self : Execution F K) (input : RowInput) :
    (if selects self input then
      Result.ok (self.roots, Charge.VerifyLfsr input.difference.len self.budget.total self.roots.count)
    else .ok (self.roots, Charge.Verify input.difference.len self.budget.total)) =
      .ok (self.roots, priceTag self input) := by
  unfold priceTag
  split <;> rfl

theorem verify_refines : ActualExecutionVerify := by
  intro K kernels self input workspace meter cost seed continued priced bounds
  obtain ⟨rootsRoom, rebuiltAdmission, fullAdmission⟩ := bounds
  unfold Execution.verify
  change Aeneas.Std.bind
    (if self.v3 then
      Aeneas.Std.bind (bulksketch.decode.verify.use_rebuilt_lfsr self.roots.count input.difference.len)
        (fun selected => .ok (self.roots, selected))
      else .ok (self.roots, false)) _ = _
  rw [dispatch_exact self input, bind_ok]
  dsimp! only
  rw [tag_exact self input, bind_ok]
  dsimp! only
  rw [StageCharge.charge_refines_with_cost fieldDictionary kernels meter (priceTag self input) cost priced,
    bind_ok]
  generalize chargeEq : StageCharge.chargeResult meter cost = charged
  obtain ⟨outcome, final⟩ := charged
  cases outcome with
  | Err error =>
    simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]
    rfl
  | Ok value =>
    cases value
    have passed : (StageCharge.chargeResult meter cost).1 = .Ok () := by rw [chargeEq]
    have roots := shared_prefix_normal workspace.roots self.roots.count (rootsRoom passed)
    change _ = Result.ok (selectedRoots self workspace) at roots
    change Aeneas.Std.bind
      (Result.ok (core.ops.control_flow.ControlFlow.Continue () :
        core.ops.control_flow.ControlFlow (core.result.Result Never DecodeError) Unit)) _ = _
    rw [bind_ok]
    simp only [Slice.index_SliceIndexRangeToUsizeSliceInst, roots, bind_ok]
    by_cases rebuilt : selects self input = true
    · have exactRebuilt := rebuilt_normal kernels (selectedRoots self workspace) input.difference workspace.bm
        workspace.verification seed continued (rebuiltAdmission passed rebuilt)
      simp only [rebuilt, ite_true]
      simp only [exactRebuilt, bind_ok]
      obtain ⟨valid, bm, verification⟩ := rebuiltExpected (selectedRoots self workspace) input.difference
        workspace.bm workspace.verification seed continued
      change Aeneas.Std.bind (Result.ok (bm, verification, valid)) _ = _
      rw [bind_ok]
      cases valid <;> rfl
    · have direct : selects self input = false := Bool.eq_false_iff.mpr rebuilt
      obtain ⟨mul, square, encode, admitted⟩ := fullAdmission passed direct
      have exactDirect := ProbeVerification.verified_refines kernels mul square encode input.difference
        (selectedRoots self workspace) workspace.verification admitted
      simp only [direct, Bool.false_eq_true, ite_false]
      simp only [exactDirect, bind_ok]
      obtain ⟨valid, verification⟩ := ProbeVerification.expected input.difference
        (selectedRoots self workspace) workspace.verification
      change Aeneas.Std.bind (Result.ok (workspace.bm, verification, valid)) _ = _
      rw [bind_ok]
      cases valid <;> rfl

end BulksketchBridge.ExecutionVerify
