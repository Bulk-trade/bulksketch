import BulksketchBridge.RootWorkBudgetMath
import BulksketchBridge.RootPendingBudget

namespace BulksketchBridge.RootRun

open Aeneas.Std RootWorkBudget
open bulksketch.decode.roots bulksketch.decode.scratch
open scoped BigOperators

/-- A depth-first frontier consists of the active factor and the live
prefix of the saved stack. The same sum accounts for reserved work and
the number of remaining proper splits. -/
def frontierCredits (credit : Nat → Nat) (roots : Roots) (stack : Slice FactorFrame) : Nat :=
  credit roots.degree.val + ∑ slot ∈ Finset.range roots.pending.val, credit (slotDegree stack slot)

abbrev frontierWork := frontierCredits rootsEnvelope
abbrev frontierSplits := frontierCredits (fun degree => degree - 1)

private theorem credit_prefix (credit : Nat → Nat) (stack next : Slice FactorFrame) (count : Nat)
    (same : ∀ slot < count, next.val[slot]? = stack.val[slot]?) :
    (∑ slot ∈ Finset.range count, credit (slotDegree next slot)) =
      ∑ slot ∈ Finset.range count, credit (slotDegree stack slot) := by
  apply Finset.sum_congr rfl
  intro slot inRange
  simp only [slotDegree, same _ (Finset.mem_range.mp inRange)]

/-- Exact arithmetic of the stack push after a proper native split. -/
theorem frontier_credits_push (credit : Nat → Nat) (roots after : Roots)
    (stack next : Slice FactorFrame) (frame : FactorFrame)
    (count : after.pending.val = roots.pending.val + 1)
    (older : ∀ slot < roots.pending.val, next.val[slot]? = stack.val[slot]?)
    (newest : next.val[roots.pending.val]? = some frame) :
    frontierCredits credit after next =
      credit after.degree.val + credit (frame.coefficient_len.val - 1) +
        ∑ slot ∈ Finset.range roots.pending.val, credit (slotDegree stack slot) := by
  unfold frontierCredits
  rw [count, Finset.sum_range_succ, credit_prefix credit stack next _ older]
  have saved : slotDegree next roots.pending.val = frame.coefficient_len.val - 1 := by
    simp only [slotDegree, newest, Option.map_some, Option.getD_some]
  rw [saved]
  omega

/-- Exact arithmetic of a pop after an emission, including transfer of
the saved factor's credit into the active slot. -/
theorem frontier_credits_pop (credit : Nat → Nat) (roots after : Roots)
    (stack next : Slice FactorFrame) (frame : FactorFrame)
    (pending : 0 < roots.pending.val)
    (count : after.pending.val = roots.pending.val - 1)
    (degree : after.degree.val = frame.coefficient_len.val - 1)
    (top : stack.val[roots.pending.val - 1]? = some frame)
    (older : ∀ slot < after.pending.val, next.val[slot]? = stack.val[slot]?) :
    frontierCredits credit after next + credit roots.degree.val = frontierCredits credit roots stack := by
  unfold frontierCredits
  rw [degree, credit_prefix credit stack next _ older, count]
  have split :
      (∑ slot ∈ Finset.range roots.pending.val, credit (slotDegree stack slot)) =
      (∑ slot ∈ Finset.range (roots.pending.val - 1), credit (slotDegree stack slot)) +
        credit (frame.coefficient_len.val - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel pending]
    rw [Finset.sum_range_succ]
    simp only [slotDegree, top, Option.map_some, Option.getD_some]
  rw [split]
  omega

theorem roots_envelope_split (left right parent : Nat) (leftPos : 0 < left) (rightPos : 0 < right)
    (minimum : 3 ≤ parent) (degree : left + right = parent) :
    nodeEnvelope parent + rootsEnvelope left + rootsEnvelope right ≤ rootsEnvelope parent := by
  have children := child_chains_le left right leftPos rightPos
  rw [degree] at children
  have chainParent : chain parent = chain (parent - 1) + nodeEnvelope parent := by
    unfold chain
    have shift : parent - 2 = (parent - 1 - 2) + 1 := by omega
    rw [shift, Finset.sum_range_succ, show parent - 1 - 2 + 3 = parent by omega]
  unfold rootsEnvelope
  rw [chainParent]
  omega

/-- A proper split spends at most the parent node's envelope and
leaves enough reserve for every live child and earlier sibling. The
split credit decreases by exactly one. -/
theorem frontier_proper_split (roots after : Roots) (stack next : Slice FactorFrame) (frame : FactorFrame)
    (count : after.pending.val = roots.pending.val + 1)
    (older : ∀ slot < roots.pending.val, next.val[slot]? = stack.val[slot]?)
    (newest : next.val[roots.pending.val]? = some frame)
    (leftPos : 0 < after.degree.val) (rightPos : 0 < frame.coefficient_len.val - 1)
    (minimum : 3 ≤ roots.degree.val)
    (degree : after.degree.val + (frame.coefficient_len.val - 1) = roots.degree.val) :
    nodeEnvelope roots.degree.val + frontierWork after next ≤ frontierWork roots stack ∧
      frontierSplits after next + 1 = frontierSplits roots stack := by
  constructor
  · have push := frontier_credits_push rootsEnvelope roots after stack next frame count older newest
    have costs := roots_envelope_split _ _ _ leftPos rightPos minimum degree
    change nodeEnvelope roots.degree.val + frontierCredits rootsEnvelope after next ≤ frontierCredits rootsEnvelope roots stack
    rw [push]
    unfold frontierCredits
    omega
  · have push := frontier_credits_push (fun degree => degree - 1) roots after stack next frame count older newest
    change frontierCredits (fun degree => degree - 1) after next + 1 =
      frontierCredits (fun degree => degree - 1) roots stack
    rw [push]
    unfold frontierCredits
    dsimp only
    omega

theorem frontier_pop_reserve (roots after : Roots) (stack next : Slice FactorFrame) (frame : FactorFrame)
    (pending : 0 < roots.pending.val)
    (count : after.pending.val = roots.pending.val - 1)
    (degree : after.degree.val = frame.coefficient_len.val - 1)
    (top : stack.val[roots.pending.val - 1]? = some frame)
    (older : ∀ slot < after.pending.val, next.val[slot]? = stack.val[slot]?) :
    frontierWork after next + rootsEnvelope roots.degree.val = frontierWork roots stack ∧
    frontierSplits after next + (roots.degree.val - 1) = frontierSplits roots stack :=
  ⟨frontier_credits_pop rootsEnvelope roots after stack next frame pending count degree top older,
    frontier_credits_pop (fun degree => degree - 1) roots after stack next frame pending count degree top older⟩

#print axioms frontier_proper_split
#print axioms frontier_pop_reserve

end BulksketchBridge.RootRun
