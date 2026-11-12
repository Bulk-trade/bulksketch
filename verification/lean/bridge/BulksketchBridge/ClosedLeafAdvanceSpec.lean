import Arithmetic.ClosedLeafGenerated
import BulksketchBridge.StageChargeSpec
import BulksketchBridge.RebuiltLfsrSpec

namespace BulksketchBridge.ClosedLeafAdvance

open Aeneas.Std bulksketch.decode.roots bulksketch.decode.scratch bulksketch.decode.work
open bulksketch.types

def stageFor (roots : Roots) : Stage :=
  if roots.degree < 3#usize then .Leaf else
    if roots.closed_form ∧ roots.degree = 3#usize then .LeafThree else
      if roots.closed_form ∧ roots.degree = 4#usize then .LeafFour else .ReducerPreparation

def usizeWord (value : Nat) : Usize := ⟨BitVec.ofNat _ value⟩

/-- State restored from the last pending frame. The affine traversal also
restores the saved base word and rank. -/
def poppedRoots (roots : Roots) (workspace : RowWorkspace) (frame : FactorFrame) : Roots :=
  { roots with
    pending := usizeWord (roots.pending.val - 1)
    degree := usizeWord (frame.coefficient_len.val - 1)
    direction := frame.next_direction
    checked := frame.split_checked != 0#u32
    affine_base := if roots.affine then workspace.factors[frame.coefficient_start.val + roots.stride.val - 1]!
      else roots.affine_base
    affine_rank := if roots.affine then UScalar.cast .Usize frame.next_direction else roots.affine_rank }

def poppedWorkspace (workspace : RowWorkspace) (frame : FactorFrame) : RowWorkspace :=
  let coefficients := Slice.from
    ((workspace.factors.val.drop frame.coefficient_start.val).take frame.coefficient_len.val)
    (by have bound := workspace.factors.property
        simp only [List.length_take, List.length_drop]
        exact (Nat.min_le_right _ _).trans (Nat.sub_le .. |>.trans bound))
  { workspace with polynomials := RebuiltLfsr.restorePrefix workspace.polynomials coefficients }

/-- Original guard, pop, offset conversions, destination size and affine
saved-base index are admitted by the pending-frame invariant. -/
def PopBounds (roots : Roots) (workspace : RowWorkspace) (frame : FactorFrame) : Prop :=
  roots.pending ≠ 0#usize ∧
  workspace.stack.val[roots.pending.val - 1]? = some frame ∧
  1 ≤ frame.coefficient_len.val ∧
  frame.coefficient_len.val ≤ workspace.polynomials.length ∧
  frame.coefficient_start.val + frame.coefficient_len.val ≤ workspace.factors.length ∧
  (roots.affine = true →
    1 ≤ frame.coefficient_start.val + roots.stride.val ∧
    frame.coefficient_start.val + roots.stride.val ≤ workspace.factors.length)

def ActualStageRefines : Prop :=
  ∀ roots : Roots, Roots.stage roots = Result.ok (stageFor roots)

def ActualRootsChargeRefines : Prop :=
  ∀ (meter : WorkMeter) (operation : Charge),
    charge meter operation = (do
      let cost ← WorkScheduleV1.cost operation
      Result.ok (StageCharge.chargeResult meter cost))

def ActualAdvanceRefines : Prop :=
  (∀ (roots : Roots) (workspace : RowWorkspace), roots.pending = 0#usize →
    Roots.advance roots workspace = Result.ok (.Verification, roots, workspace, id)) ∧
  (∀ (roots : Roots) (workspace : RowWorkspace) (frame : FactorFrame), PopBounds roots workspace frame →
    let updatedRoots := poppedRoots roots workspace frame
    Roots.advance roots workspace =
      Result.ok (stageFor updatedRoots, updatedRoots, poppedWorkspace workspace frame, id))

end BulksketchBridge.ClosedLeafAdvance
