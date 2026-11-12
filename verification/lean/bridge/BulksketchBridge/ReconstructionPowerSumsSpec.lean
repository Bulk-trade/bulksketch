import BulksketchBridge.ReconstructionWrapperSpec
import BulksketchBridge.SyndromeUniquenessSpec

namespace BulksketchBridge.Reconstruction

open Aeneas.Std Algebra.Gf64 Reconciliation bulksketch.decode bulksketch.types

/-- The admitted paid path returns the Berlekamp–Massey stage with every
positive syndrome through twice capacity represented in the quotient field. -/
def ActualReconstructionReturnsPowerSums : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : bulksketch.backend.contract.BulkKernels K F)
    (self : stages.Execution F K) (input : row.RowInput)
    (workspace : scratch.RowWorkspace) (meter : WorkMeter) (roots : Finset Algebra.Gf64.Field),
    (∀ word, kernels.ArithmeticInst.square word = .ok (squareWord word)) →
    ¬(self.budget.total = self.budget.nonzero ∧ allZero input.difference = true) →
    (StageCharge.reconstructCharge meter (Slice.len input.difference)).1 = .Ok () →
    WorkspaceAdmission.check (workspaceLengths workspace) input.difference.length self.budget.nonzero.val = true →
    (∀ i < input.difference.length, toField input.difference.val[i]!.bv = oddSyndrome roots i) →
    ∃ updated final,
      stages.Execution.reconstruct field kernels self input workspace meter =
        .ok (.Ok (.Ok (some .BerlekampMassey)), self, updated, id, final) ∧
      ∀ p, 0 < p → p ≤ 2 * input.difference.length →
        toField updated.syndromes.val[p]!.bv = powerSum roots p

end BulksketchBridge.Reconstruction
