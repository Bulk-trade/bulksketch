import Arithmetic.ReconstructionGenerated
import BulksketchBridge.ReconstructionAllZero
import BulksketchBridge.ReconstructionSpec
import BulksketchBridge.StageCharge

namespace BulksketchBridge.Reconstruction

open Aeneas.Std bulksketch.decode bulksketch.types

abbrev RowOutcome := core.result.Result (core.result.Result (Option Stage) DecodeFailure) DecodeError

def finish (charge : core.result.Result Unit DecodeError) (stage : Option Stage) : RowOutcome :=
  match charge with
  | .Ok _ => .Ok (.Ok stage)
  | .Err error => .Err error

def PaidOutcome (input : row.RowInput) (workspace : scratch.RowWorkspace)
    (budget : Usize) (charge : core.result.Result Unit DecodeError)
    (reply : RowOutcome) (updated : scratch.RowWorkspace) : Prop :=
  match charge with
  | .Err error => reply = .Err error ∧ updated = workspace
  | .Ok () =>
    if WorkspaceAdmission.check (workspaceLengths workspace) input.difference.length budget.val then
      reply = .Ok (.Ok (some .BerlekampMassey)) ∧
      ∃ syndromes, updated = {workspace with syndromes} ∧
        Prefix input.difference workspace.syndromes syndromes (2 * input.difference.length + 1)
    else reply = .Err .ScratchTooSmall ∧ updated = workspace

/-- Exact row result, state, workspace and backward frame, including meter
failures, the all-zero early path and the post-charge workspace rejection. -/
def ActualReconstructionReturnsExactFrame : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : bulksketch.backend.contract.BulkKernels K F)
    (self : stages.Execution F K) (input : row.RowInput)
    (workspace : scratch.RowWorkspace) (meter : WorkMeter),
    (∀ word, kernels.ArithmeticInst.square word = .ok (squareWord word)) →
    ∃ reply updated final,
      stages.Execution.reconstruct field kernels self input workspace meter =
        .ok (reply, self, updated, id, final) ∧
      if self.budget.total = self.budget.nonzero ∧ allZero input.difference = true then
        updated = workspace ∧
        let zeroCharge := (BulksketchBridge.WorkMeter.toModel meter).charge 0
        BulksketchBridge.WorkMeter.toModel final = zeroCharge.1 ∧
        reply = finish (BulksketchBridge.WorkMeter.rustOutcome zeroCharge.2) none
      else
        let charged := StageCharge.reconstructCharge meter (Slice.len input.difference)
        final = charged.2 ∧ PaidOutcome input workspace self.budget.nonzero charged.1 reply updated

end BulksketchBridge.Reconstruction
