import BulksketchBridge.WorkspaceAdmissionGenerated
import Workmeter.Types
import Mathlib.Tactic.Tauto

namespace BulksketchBridge.WorkspaceAdmission

open Aeneas.Std

/-- The independent capacity predicate agrees with the successful original LLBC paths. -/
theorem sourceAccepts_iff_admitted (lengths : Lengths) (capacity budget : Nat) :
    sourceAccepts lengths capacity budget ↔ Admitted lengths capacity budget := by
  by_cases zero : budget = 0
  · subst budget
    simp [sourceAccepts, Admitted]
    tauto
  · simp only [sourceAccepts, Admitted, zero, ite_false, false_and, and_false, false_or]
    tauto

/-- Exact Rust result and read-only frame for every workspace descriptor and usize input. -/
def ActualWorkspaceAdmissionReturnsExactFrame : Prop :=
  ∀ {Workspace : Type} (lengths : Workspace → Lengths) (workspace : Workspace) (capacity budget : Usize),
    runOriginal lengths workspace capacity budget =
      (if check (lengths workspace) capacity.val budget.val then .Ok () else .Err .ScratchTooSmall,
        workspace)

theorem check_workspace_refines : ActualWorkspaceAdmissionReturnsExactFrame := by
  intro Workspace lengths workspace capacity budget
  simp only [runOriginal, check, decide_eq_true_eq, sourceAccepts_iff_admitted]

theorem checked_syndrome_bounds (lengths : Lengths) (capacity budget : Nat)
    (admitted : check lengths capacity budget = true) :
    2 * capacity ≤ usizeMax ∧ 2 * capacity + 1 ≤ lengths.syndromes := by
  simp only [check, decide_eq_true_eq, Admitted] at admitted
  tauto

end BulksketchBridge.WorkspaceAdmission
