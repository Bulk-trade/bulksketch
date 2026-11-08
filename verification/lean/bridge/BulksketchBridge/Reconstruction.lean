import BulksketchBridge.ReconstructionWrapperSpec
import BulksketchBridge.ReconstructionFill

namespace BulksketchBridge.Reconstruction

open Aeneas Aeneas.Std bulksketch.decode bulksketch.types

private theorem check_normal (workspace : scratch.RowWorkspace) (capacity budget : Usize) :
    checkWorkspace workspace capacity budget =
      .ok (if WorkspaceAdmission.check (workspaceLengths workspace) capacity.val budget.val
        then .Ok () else .Err .ScratchTooSmall) := by
  unfold checkWorkspace
  rw [WorkspaceAdmission.check_workspace_refines]

private theorem admitted_room (workspace : scratch.RowWorkspace) (capacity budget : Nat)
    (admitted : WorkspaceAdmission.check (workspaceLengths workspace) capacity budget = true) :
    2 * capacity < workspace.syndromes.length := by
  have room := (WorkspaceAdmission.checked_syndrome_bounds _ _ _ admitted).2
  change 2 * capacity + 1 ≤ workspace.syndromes.length at room
  omega

theorem reconstruct_refines : ActualReconstructionReturnsExactFrame := by
  intro F K field kernels self input workspace meter square
  obtain ⟨iter, scan⟩ := all_zero_normal field kernels input.difference
  by_cases early : self.budget.total = self.budget.nonzero ∧ allZero input.difference = true
  · obtain ⟨final, charge, meterEq⟩ := BulksketchBridge.WorkMeter.charge_refines meter 0#u64
    have zero : BulksketchBridge.WorkMeter.toUInt64 0#u64 = 0 := rfl
    rw [zero] at charge meterEq
    let zeroCharge := (BulksketchBridge.WorkMeter.toModel meter).charge 0
    refine ⟨finish (BulksketchBridge.WorkMeter.rustOutcome zeroCharge.2) none, workspace, final, ?_, ?_⟩
    · cases normal : BulksketchBridge.WorkMeter.rustOutcome zeroCharge.2 <;>
        simp only [zeroCharge] at normal <;>
        simp [stages.Execution.reconstruct, early.1, early.2, core.slice.Slice.iter, scan,
          charge, normal, finish, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from] <;> rfl
    · simp only [early]
      exact ⟨by trivial, meterEq, by trivial⟩
  · have charge := StageCharge.reconstruct_refines field kernels meter (Slice.len input.difference)
    cases priced : StageCharge.reconstructCharge meter (Slice.len input.difference) with
    | mk charged final =>
      rw [priced] at charge
      have scanFalse : self.budget.total = self.budget.nonzero → allZero input.difference = false := by
        intro equal
        cases zero : allZero input.difference
        · rfl
        · exact (early ⟨equal, zero⟩).elim
      cases charged with
      | Err error =>
        refine ⟨.Err error, workspace, final, ?_, ?_⟩
        · by_cases equal : self.budget.total = self.budget.nonzero <;>
            simp [stages.Execution.reconstruct, equal, core.slice.Slice.iter, scan, scanFalse,
              charge, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.from] <;> rfl
        · simp [early, PaidOutcome]
      | Ok empty =>
        cases empty
        have checked := check_normal workspace (Slice.len input.difference) self.budget.nonzero
        rw [Slice.len_val] at checked
        cases admitted : WorkspaceAdmission.check (workspaceLengths workspace) input.difference.length
            self.budget.nonzero.val with
        | false =>
          refine ⟨.Err .ScratchTooSmall, workspace, final, ?_, ?_⟩
          · by_cases equal : self.budget.total = self.budget.nonzero <;>
              simp [stages.Execution.reconstruct, equal, core.slice.Slice.iter, scan, scanFalse,
                charge, checked, admitted, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from] <;> rfl
          · simp [early, PaidOutcome, admitted]
        | true =>
          obtain ⟨endpoint, range, words, sentinel, multiply, newRange, loop0, loop1, inv⟩ :=
            fill_normal field kernels input.difference workspace.syndromes square
              (admitted_room workspace input.difference.length self.budget.nonzero.val admitted)
          refine ⟨.Ok (.Ok (some .BerlekampMassey)), {workspace with syndromes := words}, final, ?_, ?_⟩
          · by_cases equal : self.budget.total = self.budget.nonzero <;>
              simp [stages.Execution.reconstruct, equal, core.slice.Slice.iter, scan, scanFalse,
                charge, checked, admitted, core.result.Result.Insts.CoreOpsTry.branch,
                sentinel, multiply, newRange, loop0, loop1] <;> rfl
          · simp only [early, ite_false, PaidOutcome, admitted, ite_true]
            exact ⟨by trivial, by trivial, words, rfl, inv⟩

end BulksketchBridge.Reconstruction
