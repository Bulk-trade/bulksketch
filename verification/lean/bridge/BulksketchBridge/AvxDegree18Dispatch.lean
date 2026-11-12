import BulksketchBridge.VerifyDispatch

namespace BulksketchBridge.VerifyDispatch

open Aeneas.Std

/-- Exact degree-18 selection cut including the two discontinuities
introduced by the continuation-block ceiling. -/
def degree18Wins (capacity : Nat) : Prop :=
  capacity ≤ 65535 ∧ (capacity = 98 ∨ (103 ≤ capacity ∧ capacity ≤ 106) ∨ 108 ≤ capacity)

instance (capacity : Nat) : Decidable (degree18Wins capacity) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem degree18_selects (capacity : Nat) :
    selectsRebuilt 18 capacity = decide (degree18Wins capacity) := by
  by_cases admitted : 18 ≤ capacity ∧ capacity ≤ 65535
  · simp only [selectsRebuilt, expectedCounts, admitted, and_self, ite_true, show ¬18 ≤ 2 by decide, ite_false]
    let blocks := (capacity - 18 + 7) / 8
    have blocksBound : blocks ≤ 8192 := by dsimp [blocks]; omega
    have currentFits : 8 * capacity < 2 ^ 64 := by omega
    have rawFits : 2 * (30 + 4 * 18 + 18 * blocks) + 18 < 2 ^ 64 := by omega
    have reducedFits : 6 * 30 + 8 * 18 + 3 * 18 + 40 * blocks < 2 ^ 64 := by omega
    simp only [decide_eq_decide]
    change (((2 * (30 + 4 * 18 + 18 * blocks) + 18) % (2^64) ≤ (8 * capacity) % (2^64)) ∧
      ((6 * 30 + 8 * 18 + 3 * 18 + 40 * blocks) % (2^64) ≤ (8 * capacity) % (2^64)) ∧
      (((2 * (30 + 4 * 18 + 18 * blocks) + 18) % (2^64) < (8 * capacity) % (2^64)) ∨
       ((6 * 30 + 8 * 18 + 3 * 18 + 40 * blocks) % (2^64) < (8 * capacity) % (2^64)))) ↔ degree18Wins capacity
    rw [Nat.mod_eq_of_lt currentFits, Nat.mod_eq_of_lt rawFits, Nat.mod_eq_of_lt reducedFits]
    unfold degree18Wins blocks
    omega
  · simp only [selectsRebuilt, expectedCounts, admitted, ite_false, show ¬18 ≤ 2 by decide]
    exact (decide_eq_false (by unfold degree18Wins; omega)).symm

def ActualNativeDegree18Dispatch : Prop :=
  ∀ capacity : Usize,
    bulksketch.decode.verify.use_rebuilt_lfsr 18#usize capacity = .ok (decide (degree18Wins capacity.val))

theorem native_degree18_selects : ActualNativeDegree18Dispatch := by
  intro capacity
  rw [use_rebuilt_lfsr_refines]
  exact congrArg Result.ok (degree18_selects capacity.val)

#print axioms native_degree18_selects

end BulksketchBridge.VerifyDispatch
