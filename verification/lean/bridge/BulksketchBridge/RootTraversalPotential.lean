import BulksketchBridge.RootPendingBudget
import BulksketchBridge.RootNativeAffineGcd

namespace BulksketchBridge.RootRun

open Aeneas.Std ClosedLeafAdvance RootDivide
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open scoped BigOperators

set_option maxRecDepth 4096

def pendingPotential (stack : Slice FactorFrame) (count : Nat) : Nat :=
  ∑ slot ∈ Finset.range count, slotDegree stack slot ^ 2

def traversalPotential (roots : Roots) (stack : Slice FactorFrame) : Nat :=
  roots.degree.val ^ 2 + pendingPotential stack roots.pending.val

private theorem potential_push (stack : Slice FactorFrame) (count : Usize) (frame : FactorFrame)
    (room : count.val < stack.length) :
    pendingPotential (stack.set count frame) (count.val + 1) =
      pendingPotential stack count.val + (frame.coefficient_len.val - 1) ^ 2 := by
  unfold pendingPotential
  rw [Finset.sum_range_succ]
  have new : slotDegree (stack.set count frame) count.val = frame.coefficient_len.val - 1 := by
    unfold slotDegree
    rw [Slice.set_val_eq, List.getElem?_set_self (show count.val < stack.val.length from room)]
    rfl
  rw [new]
  congr 1
  apply Finset.sum_congr rfl
  intro slot live
  unfold slotDegree
  rw [Slice.set_val_eq, List.getElem?_set_ne (Nat.ne_of_gt (Finset.mem_range.mp live))]

private theorem potential_pop (stack : Slice FactorFrame) (count : Nat) (frame : FactorFrame)
    (positive : 0 < count) (present : stack.val[count - 1]? = some frame) :
    pendingPotential stack count =
      pendingPotential stack (count - 1) + (frame.coefficient_len.val - 1) ^ 2 := by
  conv_lhs => rw [← Nat.sub_add_cancel positive]
  unfold pendingPotential
  rw [Finset.sum_range_succ]
  simp only [slotDegree, present, Option.map_some, Option.getD_some]

/-- A proper native split strictly decreases the sum of squared live degrees. -/
theorem committed_potential_decreases (roots : Roots) (buffers : FactorWork) (factors : Slice U64)
    (stack : Slice FactorFrame) (meter : WorkMeter) (length start : Usize)
    (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (slot : roots.pending.val < stack.length)
    (degree : roots.gcd_degree.val + (length.val - 1) = roots.degree.val)
    (leftPositive : 0 < roots.gcd_degree.val) (rightPositive : 0 < length.val - 1) :
    let output := committed roots buffers factors stack meter length start quotient remainder raw
    traversalPotential output.2.1 output.2.2.2.2.2.1 < traversalPotential roots stack := by
  have pendingMax : roots.pending.val + 1 ≤ Usize.max :=
    (Nat.succ_le_of_lt slot).trans stack.length_ineq
  have added : (usizeWord (roots.pending.val + 1)).val = roots.pending.val + 1 := word_val _ pendingMax
  let frame : FactorFrame := ⟨UScalar.cast .U64 start, UScalar.cast .U64 length, directionWord roots, 1#u32⟩
  have exactLen : frame.coefficient_len.val = length.val := by
    change (UScalar.cast .U64 length).val = length.val
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (length.hBounds.trans_le (Nat.pow_le_pow_right (by decide) System.Platform.numBits_le))
  have strict : roots.gcd_degree.val ^ 2 + (length.val - 1) ^ 2 < roots.degree.val ^ 2 := by
    rw [← degree]
    calc
      _ < roots.gcd_degree.val ^ 2 + (length.val - 1) ^ 2 +
          2 * (roots.gcd_degree.val * (length.val - 1)) :=
        Nat.lt_add_of_pos_right (Nat.mul_pos (by decide) (Nat.mul_pos leftPositive rightPositive))
      _ = _ := by ring
  cases affine : roots.affine with
  | false =>
    simp only [committed, affine, Bool.false_eq_true, ite_false, traversalPotential, added]
    change roots.gcd_degree.val ^ 2 + pendingPotential (stack.set roots.pending frame) (roots.pending.val + 1) < _
    rw [potential_push _ _ _ slot, exactLen]
    omega
  | true =>
    let saved := { frame with next_direction := UScalar.cast .U32 (usizeWord (roots.affine_rank.val - 1)) }
    have collapsed : (stack.set roots.pending frame).set roots.pending saved = stack.set roots.pending saved := by
      apply Slice.ext
      simp only [Slice.set_val_eq, List.set_set]
    simp only [committed, affine, ite_true, traversalPotential, added]
    change roots.gcd_degree.val ^ 2 +
      pendingPotential ((stack.set roots.pending frame).set roots.pending saved) (roots.pending.val + 1) < _
    rw [collapsed, potential_push _ _ _ slot]
    change roots.gcd_degree.val ^ 2 +
      (pendingPotential stack roots.pending.val + (frame.coefficient_len.val - 1) ^ 2) < _
    rw [exactLen]
    omega

/-- Emitting a nonempty active leaf removes precisely its squared degree,
    even when the pop makes a larger pending factor active. -/
theorem popped_potential_decreases (roots : Roots) (workspace : RowWorkspace) (frame : FactorFrame)
    (active : PopBounds roots workspace frame) (nonconstant : 0 < roots.degree.val) :
    traversalPotential (poppedRoots roots workspace frame) (poppedWorkspace workspace frame).stack <
      traversalPotential roots workspace.stack := by
  obtain ⟨notEmpty, present, _, lengthRoom, _, _⟩ := active
  have positive : 0 < roots.pending.val := by
    apply Nat.pos_of_ne_zero
    intro zero
    exact notEmpty (UScalar.eq_of_val_eq zero)
  have remaining : (usizeWord (roots.pending.val - 1)).val = roots.pending.val - 1 :=
    word_val _ ((Nat.sub_le ..).trans (by scalar_tac))
  have copied : (usizeWord (frame.coefficient_len.val - 1)).val = frame.coefficient_len.val - 1 :=
    word_val _ ((Nat.sub_le ..).trans (lengthRoom.trans workspace.polynomials.length_ineq))
  simp only [traversalPotential, poppedRoots, poppedWorkspace, remaining, copied]
  rw [potential_pop _ _ _ positive present]
  have squarePositive : 0 < roots.degree.val ^ 2 := Nat.pow_pos nonconstant
  omega

#print axioms committed_potential_decreases
#print axioms popped_potential_decreases

end BulksketchBridge.RootRun
