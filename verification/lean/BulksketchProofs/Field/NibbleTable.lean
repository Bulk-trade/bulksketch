import BulksketchProofs.Field.CLMul

/-! Fixed nibble arithmetic supporting the original first multiplication loop.
Only the fifteen nonzero table indices are enumerated; the input word is universal. -/

namespace BulksketchProofs.Field

/-- Every source table recurrence uses an earlier initialized entry and a shift below four. -/
theorem nibble_low_bit_bounds (index : Nat) (positive : 0 < index) (small : index < 16) :
    (index &&& (index - 1)) < index ∧ (index &&& (index - 1)) < 16 ∧
      (BitVec.ofNat 4 index).ctz.toNat < 4 ∧
      (BitVec.ofNat 4 index).ctz.toNat < 128 := by
  have indexCases : index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 := by omega
  rcases indexCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst index; decide

/-- Zero selects no polynomial contribution. -/
theorem nibbleMultiple_zero (left : BitVec 64) : nibbleMultiple left 0 = 0 := by
  simp [nibbleMultiple, clmulPrefix]

/-- Clearing the lowest set bit gives exactly the source nibble-table recurrence. -/
theorem nibble_clear_low_bit (left : BitVec 64) (index : Nat)
    (positive : 0 < index) (small : index < 16) :
    nibbleMultiple left (BitVec.ofNat 4 index) =
      nibbleMultiple left (BitVec.ofNat 4 (index &&& (index - 1))) ^^^
        (left.setWidth 128 <<< (BitVec.ofNat 4 index).ctz.toNat) := by
  have indexCases : index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 := by omega
  rcases indexCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    subst index
    simp [nibbleMultiple, clmulPrefix, BitVec.ctz, BitVec.clz, BitVec.clzAuxRec,
      BitVec.getLsbD_reverse,
      -BitVec.getLsbD_eq_getElem]
    try ac_rfl

end BulksketchProofs.Field
