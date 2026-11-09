import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace BulksketchBridge.RootWorkBudget

open scoped BigOperators

def tableUnits (degree : Nat) : Nat := 8 * degree * degree + 2 * degree
def squareUnits (degree : Nat) : Nat := 3 * degree * degree + 2 * degree
def traceUnits (degree : Nat) : Nat := 63 * (squareUnits degree + 2)
def splitCheckUnits (degree : Nat) : Nat := squareUnits degree + degree + 1
def gcdUnits (degree : Nat) : Nat := 8 * (degree + 1) ^ 2 + 128 * (degree + 1)
def divideUnits (degree : Nat) : Nat := 4 * (degree + 1) ^ 2 + 128
def assemblyUnits (degree : Nat) : Nat := 4 * (degree + 1)

def nodeEnvelope (degree : Nat) : Nat :=
  12812 * degree ^ 2 + 17486 * degree + 16968

theorem node_envelope_expanded (degree : Nat) :
    tableUnits degree + 64 * (traceUnits degree + splitCheckUnits degree + gcdUnits degree) +
      divideUnits degree + assemblyUnits degree = nodeEnvelope degree := by
  unfold tableUnits traceUnits splitCheckUnits squareUnits gcdUnits divideUnits assemblyUnits nodeEnvelope
  ring

/-- A traversal node can install one reducer, try at most 64
    directions, and commit at most one proper split. -/
structure NodeCounts where
  table : Nat
  trace : Nat
  splitCheck : Nat
  gcd : Nat
  divide : Nat
  assembly : Nat

def NodeCounts.units (counts : NodeCounts) (degree : Nat) : Nat :=
  counts.table * tableUnits degree + counts.trace * traceUnits degree +
    counts.splitCheck * splitCheckUnits degree + counts.gcd * gcdUnits degree +
    counts.divide * divideUnits degree + counts.assembly * assemblyUnits degree

theorem node_counts_fit (degree : Nat) (counts : NodeCounts)
    (table : counts.table ≤ 1) (trace : counts.trace ≤ 64) (splitCheck : counts.splitCheck ≤ 64)
    (gcd : counts.gcd ≤ 64) (divide : counts.divide ≤ 1) (assembly : counts.assembly ≤ 1) :
    counts.units degree ≤ nodeEnvelope degree := by
  unfold NodeCounts.units
  calc
    _ ≤ 1 * tableUnits degree + 64 * traceUnits degree +
        64 * splitCheckUnits degree + 64 * gcdUnits degree +
        1 * divideUnits degree + 1 * assemblyUnits degree :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ table) (Nat.mul_le_mul_right _ trace))
        (Nat.mul_le_mul_right _ splitCheck)) (Nat.mul_le_mul_right _ gcd))
        (Nat.mul_le_mul_right _ divide)) (Nat.mul_le_mul_right _ assembly)
    _ = nodeEnvelope degree := by
      rw [← node_envelope_expanded]
      ring

theorem nodeEnvelope_mono : Monotone nodeEnvelope := by
  intro degree budget bound
  unfold nodeEnvelope
  exact Nat.add_le_add_right (Nat.add_le_add
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bound _)) (Nat.mul_le_mul_left _ bound)) _

def chain (degree : Nat) : Nat :=
  ∑ i ∈ Finset.range (degree - 2), nodeEnvelope (i + 3)

private theorem chain_step (degree : Nat) (minimum : 2 ≤ degree) :
    chain (degree + 1) = chain degree + nodeEnvelope (degree + 1) := by
  unfold chain
  rw [show degree + 1 - 2 = (degree - 2) + 1 by omega, Finset.sum_range_succ,
    show degree - 2 + 3 = degree + 1 by omega]

theorem chain_mono : Monotone chain := by
  apply monotone_nat_of_le_succ
  intro degree
  by_cases minimum : 2 ≤ degree
  · rw [chain_step degree minimum]
    exact Nat.le_add_right ..
  · simp only [chain, show degree - 2 = 0 by omega, show degree + 1 - 2 = 0 by omega,
      Finset.range_zero, Finset.sum_empty, Nat.le_refl]

/-- Any proper binary split has a total child chain bounded by the
    original chain below the parent. Only monotonicity is required. -/
theorem child_chains_le (left right : Nat) (leftPositive : 0 < left) (rightPositive : 0 < right) :
    chain left + chain right ≤ chain (left + right - 1) := by
  induction right with
  | zero => omega
  | succ right ih =>
    by_cases short : right ≤ 1
    · have empty : chain (right + 1) = 0 := by
        simp only [chain, show right + 1 - 2 = 0 by omega, Finset.range_zero, Finset.sum_empty]
      rw [empty, Nat.add_zero]
      exact chain_mono (by omega)
    · have below := ih (by omega)
      rw [chain_step right (by omega), show left + (right + 1) - 1 = (left + right - 1) + 1 by omega,
        chain_step (left + right - 1) (by omega), ← Nat.add_assoc]
      exact Nat.add_le_add below (nodeEnvelope_mono (by omega))

def rootsEnvelope (degree : Nat) : Nat := 160 * degree + chain degree

theorem rootsEnvelope_mono : Monotone rootsEnvelope := by
  intro degree budget bounded
  exact Nat.add_le_add (Nat.mul_le_mul_left _ bounded) (chain_mono bounded)

/-- Charges on a degree-conserving proper split tree. The zero-degree
    and degree-one/two leaves use the same envelope as the source. -/
inductive ChargedFactorTree : Nat → Nat → Prop where
  | leaf {degree charged : Nat} : degree ≤ 2 → charged ≤ 160 * degree →
      ChargedFactorTree degree charged
  | split {left right localCharge leftCharge rightCharge : Nat} :
      0 < left → 0 < right → 3 ≤ left + right →
      localCharge ≤ nodeEnvelope (left + right) →
      ChargedFactorTree left leftCharge → ChargedFactorTree right rightCharge →
      ChargedFactorTree (left + right) (localCharge + leftCharge + rightCharge)

theorem proper_binary_tree_bound {degree charged budget : Nat}
    (tree : ChargedFactorTree degree charged) (budgeted : degree ≤ budget) :
    charged ≤ rootsEnvelope budget := by
  apply Nat.le_trans _ (rootsEnvelope_mono budgeted)
  induction tree with
  | leaf _ cost =>
    exact cost.trans (Nat.le_add_right ..)
  | @split left right localCharge leftCharge rightCharge leftPos rightPos minimum localBound leftTree rightTree ihLeft ihRight =>
    have children := child_chains_le left right leftPos rightPos
    have expand : chain (left + right) = chain (left + right - 1) + nodeEnvelope (left + right) := by
      have step := chain_step (left + right - 1) (by omega)
      simpa only [show left + right - 1 + 1 = left + right by omega] using step
    unfold rootsEnvelope at ihLeft ihRight ⊢
    rw [Nat.mul_add, expand]
    omega

private theorem squares_sum_times_six (degree : Nat) :
    6 * (∑ i ∈ Finset.range (degree + 1), i ^ 2) = degree * (degree + 1) * (2 * degree + 1) := by
  induction degree with
  | zero => decide
  | succ degree ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

theorem closed_squares (degree : Nat) (minimum : 3 ≤ degree) :
    (∑ i ∈ Finset.range (degree - 2), (i + 3) ^ 2) =
      degree * (degree + 1) * (2 * degree + 1) / 6 - 5 := by
  have split : 3 + (degree - 2) = degree + 1 := by omega
  have series := squares_sum_times_six degree
  have tail : (∑ i ∈ Finset.range (degree + 1), i ^ 2) =
      5 + ∑ i ∈ Finset.range (degree - 2), (i + 3) ^ 2 := by
    rw [← split, Finset.sum_range_add]
    norm_num [Finset.sum_range_succ, Nat.add_comm]
  rw [tail] at series
  omega

theorem closed_linear (degree : Nat) (minimum : 3 ≤ degree) :
    (∑ i ∈ Finset.range (degree - 2), (i + 3)) = degree * (degree + 1) / 2 - 3 := by
  have split : 3 + (degree - 2) = degree + 1 := by omega
  have tail : (∑ i ∈ Finset.range (degree + 1), i) =
      3 + ∑ i ∈ Finset.range (degree - 2), (i + 3) := by
    rw [← split, Finset.sum_range_add]
    norm_num [Finset.sum_range_succ, Nat.add_comm]
  have closed : (∑ i ∈ Finset.range (degree + 1), i) = degree * (degree + 1) / 2 := by
    rw [Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm (degree + 1) degree]
  have total := tail.symm.trans closed
  omega

def closedRoots (degree : Nat) : Nat :=
  160 * degree + if degree < 3 then 0 else
    12812 * (degree * (degree + 1) * (2 * degree + 1) / 6 - 5) +
      17486 * (degree * (degree + 1) / 2 - 3) + 16968 * (degree - 2)

theorem roots_envelope_closed (degree : Nat) : rootsEnvelope degree = closedRoots degree := by
  unfold rootsEnvelope closedRoots chain
  by_cases small : degree < 3
  · simp only [small, ite_true, show degree - 2 = 0 by omega, Finset.range_zero, Finset.sum_empty]
  · simp only [small, ite_false, nodeEnvelope]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      closed_squares degree (by omega), closed_linear degree (by omega)]
    simp only [Nat.cast_id]
    ring

#print axioms proper_binary_tree_bound
#print axioms roots_envelope_closed

end BulksketchBridge.RootWorkBudget
