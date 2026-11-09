import BulksketchBridge.RootPendingFactors
import BulksketchBridge.RootWorkspaceBudget

namespace BulksketchBridge.RootRun

open Aeneas.Std ClosedLeafAdvance
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 1700000

def slotDegree (stack : Slice FactorFrame) (slot : Nat) : Nat :=
  (stack.val[slot]?.map fun frame => frame.coefficient_len.val - 1).getD 0

def pendingDegree (stack : Slice FactorFrame) (count : Nat) : Nat :=
  ∑ slot ∈ Finset.range count, slotDegree stack slot

def factorDegreeMass (roots : Roots) (stack : Slice FactorFrame) : Nat :=
  roots.count.val + roots.degree.val + pendingDegree stack roots.pending.val

theorem positive_slots_bound (stack : Slice FactorFrame) (count : Nat)
    (positive : ∀ slot < count, 0 < slotDegree stack slot) :
    count ≤ pendingDegree stack count := by
  have lower : (∑ _slot ∈ Finset.range count, (1 : Nat)) ≤ pendingDegree stack count := by
    apply Finset.sum_le_sum
    intro slot live
    exact positive slot (Finset.mem_range.mp live)
  simpa using lower

theorem pending_degree_push (stack : Slice FactorFrame) (count : Usize) (frame : FactorFrame)
    (room : count.val < stack.length) :
    pendingDegree (stack.set count frame) (count.val + 1) =
      pendingDegree stack count.val + (frame.coefficient_len.val - 1) := by
  unfold pendingDegree
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

theorem pending_degree_pop (stack : Slice FactorFrame) (count : Nat) (frame : FactorFrame)
    (positive : 0 < count) (present : stack.val[count - 1]? = some frame) :
    pendingDegree stack count = pendingDegree stack (count - 1) + (frame.coefficient_len.val - 1) := by
  conv_lhs => rw [← Nat.sub_add_cancel positive]
  unfold pendingDegree
  rw [Finset.sum_range_succ]
  simp only [slotDegree, present, Option.map_some, Option.getD_some]

/-- Source-sized storage admits the next pending frame when every live
    frame is nonconstant and the accounted degrees fit the row budget. -/
theorem commit_slot_of_budget (roots : Roots) (workspace : RowWorkspace) (capacity budget : Nat)
    (sized : BudgetBuffers workspace capacity budget)
    (stride : roots.stride.val ≤ budget + 1) (nonconstant : 0 < roots.degree.val)
    (positive : ∀ slot < roots.pending.val, 0 < slotDegree workspace.stack slot)
    (mass : factorDegreeMass roots workspace.stack ≤ budget) :
    roots.pending.val + 1 ≤ workspace.stack.length ∧
      (roots.pending.val + 1) * roots.stride.val ≤ workspace.factors.length := by
  have pending := positive_slots_bound workspace.stack roots.pending.val positive
  unfold factorDegreeMass at mass
  have room : roots.pending.val + 1 ≤ budget := by omega
  have factors : (roots.pending.val + 1) * roots.stride.val ≤ (budget + 1) * (budget + 1) :=
    Nat.mul_le_mul (by omega) stride
  have widened : (budget + 1) * (budget + 1) ≤ 2 * ((budget + 1) * (budget + 1)) := by omega
  exact ⟨room.trans sized.stack, factors.trans (widened.trans sized.factors)⟩

open RootDivide in
/-- The exact original commit transfers the parent degree to the active
    GCD and a newly owned quotient slot. Earlier pending degrees are intact. -/
theorem committed_degree_mass (roots : Roots) (buffers : FactorWork) (factors : Slice U64)
    (stack : Slice FactorFrame) (meter : WorkMeter) (length start : Usize)
    (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (slot : roots.pending.val < stack.length)
    (degree : roots.gcd_degree.val + (length.val - 1) = roots.degree.val) :
    let output := committed roots buffers factors stack meter length start quotient remainder raw
    factorDegreeMass output.2.1 output.2.2.2.2.2.1 = factorDegreeMass roots stack := by
  have pendingMax : roots.pending.val + 1 ≤ Usize.max :=
    (Nat.succ_le_of_lt slot).trans stack.length_ineq
  have added : (usizeWord (roots.pending.val + 1)).val = roots.pending.val + 1 := word_val _ pendingMax
  let frame : FactorFrame := ⟨UScalar.cast .U64 start, UScalar.cast .U64 length, directionWord roots, 1#u32⟩
  have exactLen : frame.coefficient_len.val = length.val := by
    change (UScalar.cast .U64 length).val = length.val
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (length.hBounds.trans_le (Nat.pow_le_pow_right (by decide) System.Platform.numBits_le))
  cases affine : roots.affine with
  | false =>
    simp only [committed, affine, Bool.false_eq_true, ite_false, factorDegreeMass, added]
    change roots.count.val + roots.gcd_degree.val +
      pendingDegree (stack.set roots.pending frame) (roots.pending.val + 1) = _
    rw [pending_degree_push _ _ _ slot, exactLen]
    omega
  | true =>
    let saved := { frame with next_direction := UScalar.cast .U32 (usizeWord (roots.affine_rank.val - 1)) }
    have collapsed : (stack.set roots.pending frame).set roots.pending saved = stack.set roots.pending saved := by
      apply Slice.ext
      simp only [Slice.set_val_eq, List.set_set]
    simp only [committed, affine, ite_true, factorDegreeMass, added]
    change roots.count.val + roots.gcd_degree.val +
      pendingDegree ((stack.set roots.pending frame).set roots.pending saved) (roots.pending.val + 1) = _
    rw [collapsed, pending_degree_push _ _ _ slot]
    change roots.count.val + roots.gcd_degree.val +
      (pendingDegree stack roots.pending.val + (frame.coefficient_len.val - 1)) = _
    rw [exactLen]
    omega

/-- A leaf that emits its complete degree and advances to a pending
    factor preserves the same degree accounting. -/
theorem popped_degree_mass (roots : Roots) (workspace : RowWorkspace) (frame : FactorFrame)
    (active : PopBounds roots workspace frame) :
    let counted := { roots with count := usizeWord (roots.count.val + roots.degree.val) }
    roots.count.val + roots.degree.val ≤ Usize.max →
    factorDegreeMass (poppedRoots counted workspace frame) (poppedWorkspace workspace frame).stack =
      factorDegreeMass roots workspace.stack := by
  dsimp only
  intro countRoom
  obtain ⟨notEmpty, present, lengthPositive, lengthRoom, _, _⟩ := active
  have positive : 0 < roots.pending.val := by
    apply Nat.pos_of_ne_zero
    intro zero
    exact notEmpty (UScalar.eq_of_val_eq zero)
  have remaining : (usizeWord (roots.pending.val - 1)).val = roots.pending.val - 1 :=
    word_val _ ((Nat.sub_le ..).trans (by scalar_tac))
  have copied : (usizeWord (frame.coefficient_len.val - 1)).val = frame.coefficient_len.val - 1 :=
    word_val _ ((Nat.sub_le ..).trans (lengthRoom.trans workspace.polynomials.length_ineq))
  simp only [factorDegreeMass, poppedRoots, poppedWorkspace, remaining, copied, word_val _ countRoom]
  rw [pending_degree_pop _ _ _ positive present]
  omega

end BulksketchBridge.RootRun
