import BulksketchBridge.CandidateOffsets

namespace BulksketchBridge.CandidateNormalization

open Aeneas.Std

def HistogramMass (state : CompactState) : Prop :=
  countMass state.offsets = state.used ∧ state.offsets[0]!.val = 0

private theorem sum_bump (words : List U64) (slot : Nat) (replacement : U64)
    (room : slot < words.length) (val : replacement.val = words[slot]!.val + 1) :
    ((words.set slot replacement).map UScalar.val).sum = (words.map UScalar.val).sum + 1 := by
  induction words generalizing slot with
  | nil => simp at room
  | cons word rest ih =>
    cases slot with
    | zero =>
      change replacement.val + (rest.map UScalar.val).sum = word.val + (rest.map UScalar.val).sum + 1
      rw [List.getElem!_cons_zero] at val
      omega
    | succ slot =>
      have active : slot < rest.length := by simp only [List.length_cons] at room; omega
      have next : replacement.val = rest[slot]!.val + 1 := by simpa only [List.getElem!_cons_succ] using val
      change word.val + ((rest.set slot replacement).map UScalar.val).sum = word.val + (rest.map UScalar.val).sum + 1
      rw [ih slot active next]
      omega

private theorem compact_mass_step (buckets index : Nat) (state : CompactState)
    (active : index < state.ids.length) (bounds : CompactBounds buckets index state)
    (mass : HistogramMass state) : HistogramMass (compactAt buckets index state) := by
  unfold compactAt
  dsimp only
  split
  · exact mass
  · let id := state.ids[index]!
    let slot := id.val % buckets + 1
    have positive := bounds.1
    have room := bounds.2.1
    have slotRoom : slot < state.offsets.length := by
      have inside := Nat.mod_lt id.val positive
      unfold slot
      omega
    have slotCount := bounds.2.2.2.2 slot slotRoom
    have idRoom := bounds.2.2.1
    have max : state.ids.length ≤ Usize.max := state.ids.length_ineq
    have usizeMax : Usize.max ≤ U64.max := by
      rcases Usize.bounds_eq with b | b
      · rw [b, U32.max_eq, U64.max_eq]; decide
      · rw [b]
    let replacement := AffineSelector.word (state.offsets[slot]!.val + 1)
    have fits : state.offsets[slot]!.val + 1 ≤ U64.max := by omega
    have replacementVal : replacement.val = state.offsets.val[slot]!.val + 1 := by
      rw [← Slice.getElem!_Nat_eq]
      exact AffineSelector.word_val _ fits
    refine ⟨?_, ?_⟩
    · change ((state.offsets.setAtNat slot replacement).val.map UScalar.val).sum = state.used + 1
      simp only [Slice.setAtNat, Slice.from_val]
      rw [sum_bump _ _ _ slotRoom replacementVal]
      exact congrArg (· + 1) mass.1
    · have kept : (state.offsets.setAtNat slot replacement)[0]! = state.offsets[0]! := by
        simp only [Slice.getElem!_Nat_eq]
        exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by unfold slot; omega)
      change (state.offsets.setAtNat slot replacement)[0]!.val = 0
      rw [kept]
      exact mass.2

theorem compact_at_lengths (buckets index : Nat) (state : CompactState) :
    (compactAt buckets index state).ids.length = state.ids.length ∧
      (compactAt buckets index state).offsets.length = state.offsets.length := by
  unfold compactAt
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · simp only [addCompacted, Slice.setAtNat_length, and_self]

/-- Every accepted distinct occurrence increments exactly one bucket
counter. Offset zero stays zero and both physical buffers keep their width. -/
theorem compact_histogram (buckets fuel index : Nat) (state : CompactState)
    (room : index + fuel ≤ state.ids.length)
    (bounds : CompactBounds buckets index state) (mass : HistogramMass state) :
    let final := compactFrom buckets fuel index state
    HistogramMass final ∧ final.ids.length = state.ids.length ∧ final.offsets.length = state.offsets.length := by
  induction fuel generalizing index state with
  | zero => exact ⟨mass, rfl, rfl⟩
  | succ fuel ih =>
    have active : index < state.ids.length := by omega
    have next := compact_at_bounds buckets index state active bounds
    have nextMass := compact_mass_step buckets index state active bounds mass
    obtain ⟨idLen, offsetLen⟩ := compact_at_lengths buckets index state
    obtain ⟨final, finalIds, finalOffsets⟩ := ih (index + 1) (compactAt buckets index state)
      (by rw [idLen]; omega) next nextMass
    exact ⟨final, finalIds.trans idLen, finalOffsets.trans offsetLen⟩

#print axioms compact_histogram

end BulksketchBridge.CandidateNormalization
