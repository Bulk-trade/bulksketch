-- Generated from the frozen check_workspace LLBC by project.py.
import BulksketchBridge.WorkspaceAdmissionSpec
import Workmeter.Types

namespace BulksketchBridge.WorkspaceAdmission

/-- Successful normal paths of the original LLBC. Every other return is ScratchTooSmall. -/
def sourceAccepts (lengths : Lengths) (capacity budget : Nat) : Prop :=
  ((budget + 1) ≤ usizeMax ∧
    budget = 0 ∧
    (2 * capacity) ≤ usizeMax ∧
    ((2 * capacity) + 1) ≤ usizeMax ∧
    lengths.syndromes ≥ ((2 * capacity) + 1) ∧
    (capacity + 1) ≤ usizeMax ∧
    (4 * (capacity + 1)) ≤ usizeMax ∧
    lengths.bm ≥ (4 * (capacity + 1)) ∧
    lengths.polynomials ≥ 0 ∧
    lengths.factors ≥ 0 ∧
    (budget * (budget / 2)) ≤ usizeMax ∧
    lengths.squareTable ≥ (budget * (budget / 2)) ∧
    lengths.verification ≥ capacity ∧
    lengths.roots ≥ budget ∧
    lengths.raw ≥ 0 ∧
    lengths.stack ≥ budget) ∨
  ((budget + 1) ≤ usizeMax ∧
    budget ≠ 0 ∧
    (8 * (budget + 1)) ≤ usizeMax ∧
    ((budget + 1) * (budget + 1)) ≤ usizeMax ∧
    (2 * ((budget + 1) * (budget + 1))) ≤ usizeMax ∧
    (budget + 2) ≤ usizeMax ∧
    (2 * (budget + 2)) ≤ usizeMax ∧
    (2 * capacity) ≤ usizeMax ∧
    ((2 * capacity) + 1) ≤ usizeMax ∧
    lengths.syndromes ≥ ((2 * capacity) + 1) ∧
    (capacity + 1) ≤ usizeMax ∧
    (4 * (capacity + 1)) ≤ usizeMax ∧
    lengths.bm ≥ (4 * (capacity + 1)) ∧
    lengths.polynomials ≥ (8 * (budget + 1)) ∧
    lengths.factors ≥ (2 * ((budget + 1) * (budget + 1))) ∧
    (budget * (budget / 2)) ≤ usizeMax ∧
    lengths.squareTable ≥ (budget * (budget / 2)) ∧
    lengths.verification ≥ capacity ∧
    lengths.roots ≥ budget ∧
    lengths.raw ≥ (2 * (budget + 2)) ∧
    lengths.stack ≥ budget)

open Aeneas.Std

instance (lengths : Lengths) (capacity budget : Nat) : Decidable (sourceAccepts lengths capacity budget) := by
  unfold sourceAccepts
  infer_instance

/-- The original shared workspace is preserved on every decoded return path. -/
def runOriginal {Workspace : Type} (lengths : Workspace → Lengths) (workspace : Workspace)
    (capacity budget : Usize) : core.result.Result Unit bulksketch.types.DecodeError × Workspace :=
  (if sourceAccepts (lengths workspace) capacity.val budget.val then .Ok () else .Err .ScratchTooSmall,
    workspace)

end BulksketchBridge.WorkspaceAdmission
