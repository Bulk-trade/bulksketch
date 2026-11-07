import BulksketchBridge.RawMulTable

namespace BulksketchBridge.FrobeniusTables

open Aeneas Aeneas.Std

/-- An array value at a natural index. Source reads always establish the bound
before using this notation. -/
def entry {α : Type} {length : Usize} [Inhabited α] (array : Array α length)
    (index : Nat) : α := array.val[index]!

theorem read_normal {α : Type} {length : Usize} [Inhabited α] (array : Array α length)
    (index : Usize) (bounded : index.val < length.val) :
    Array.index_usize array index = Result.ok (entry array index.val) := by
  have inside : index.val < array.val.length := by simpa only [Array.property] using bounded
  simp only [Array.index_usize, Array.getElem?_Usize_eq, List.getElem?_eq_getElem inside, entry]
  rw [List.Inhabited_getElem_eq_getElem! _ _ inside]

theorem update_normal {α : Type} {length : Usize} (array : Array α length)
    (index : Usize) (value : α) (bounded : index.val < length.val) :
    Array.update array index value = Result.ok (array.set index value) := by
  obtain ⟨updated, normal, equal⟩ := RawMulTable.normal_of_spec _ _
    (Array.update_spec array index value (by simpa only [Array.property] using bounded))
  exact normal.trans (congrArg Result.ok equal)

theorem read_mut_normal {α : Type} {length : Usize} [Inhabited α] (array : Array α length)
    (index : Usize) (bounded : index.val < length.val) :
    Array.index_mut_usize array index = Result.ok (entry array index.val, array.set index) := by
  simp only [Array.index_mut_usize, read_normal array index bounded, Bind.bind, bind_ok]

theorem entry_set_same {α : Type} {length : Usize} [Inhabited α] (array : Array α length)
    (index : Usize) (value : α) (bounded : index.val < length.val) :
    entry (array.set index value) index.val = value := by
  simpa only [entry, Array.getElem!_Nat_eq] using
    (Array.getElem!_Nat_set_eq array index index.val value
      ⟨rfl, by simpa only [Array.property] using bounded⟩)

theorem entry_set_other {α : Type} {length : Usize} [Inhabited α] (array : Array α length)
    (index : Usize) (other : Nat) (value : α) (different : index.val ≠ other) :
    entry (array.set index value) other = entry array other := by
  simpa only [entry, Array.getElem!_Nat_eq] using
    Array.getElem!_Nat_set_ne array index other value different

theorem entry_repeat {α : Type} [Inhabited α] (length : Usize) (value : α)
    (index : Nat) (bounded : index < length.val) :
    entry (Array.repeat length value) index = value := by
  simp only [entry, Array.repeat_val, List.getElem!_eq_getElem?_getD,
    List.getElem?_replicate, bounded, ite_true, Option.getD_some]

theorem usize_succ (value : Usize) (bound : value.val < 128) :
    ∃ next : Usize, value + 1#usize = Result.ok next ∧ next.val = value.val + 1 := by
  simpa only [show (1#usize).val = 1 by simp] using
    RawMulTable.normal_of_spec _ _ (Usize.add_spec (x := value) (y := 1#usize) (by scalar_tac))

theorem u32_succ (value : U32) (bound : value.val < 128) :
    ∃ next : U32, value + 1#u32 = Result.ok next ∧ next.val = value.val + 1 := by
  simpa only [show (1#u32).val = 1 by simp] using
    RawMulTable.normal_of_spec _ _ (U32.add_spec (x := value) (y := 1#u32) (by scalar_tac))

/-- Total correctness of a source loop with a checked incrementing index. -/
theorem counted_loop {State Output : Type} (limit : Nat)
    (body : State → Usize → Result (ControlFlow (State × Usize) Output))
    (invariant : State → Nat → Prop) (finish : State → Usize → Output)
    (advance : ∀ state index, index.val < limit → invariant state index.val →
      ∃ updated next, body state index = Result.ok (.cont (updated, next)) ∧
        next.val = index.val + 1 ∧ invariant updated next.val)
    (terminal : ∀ state index, index.val = limit → body state index = Result.ok (.done (finish state index)))
    (state : State) (index : Usize) (bound : index.val ≤ limit)
    (correct : invariant state index.val) :
    ∃ final last, loop (fun (state, index) => body state index) (state, index) =
      Result.ok (finish final last) ∧ last.val = limit ∧ invariant final limit := by
  have complete : loop (fun (state, index) => body state index) (state, index) ⦃ output =>
      ∃ final last, output = finish final last ∧ last.val = limit ∧ invariant final limit ⦄ := by
    apply loop.spec_decr_nat (fun state : State × Usize => limit - state.2.val)
      (fun state => state.2.val ≤ limit ∧ invariant state.1 state.2.val)
    · intro current currentCorrect
      rcases current with ⟨current, index⟩
      change index.val ≤ limit ∧ invariant current index.val at currentCorrect
      obtain ⟨bounded, inv⟩ := currentCorrect
      by_cases active : index.val < limit
      · obtain ⟨updated, next, normal, nextValue, updatedCorrect⟩ := advance current index active inv
        have nextBound : next.val ≤ limit := by omega
        have decreases : limit - next.val < limit - index.val := by omega
        dsimp only
        rw [normal]
        exact (WP.spec_ok _).mpr ⟨⟨nextBound, updatedCorrect⟩, decreases⟩
      · have last : index.val = limit := by omega
        dsimp only
        rw [terminal current index last]
        exact (WP.spec_ok _).mpr ⟨current, index, rfl, last, last ▸ inv⟩
    · exact ⟨bound, correct⟩
  obtain ⟨output, normal, final, last, shape, lastValue, finalCorrect⟩ :=
    RawMulTable.normal_of_spec _ _ complete
  exact ⟨final, last, normal.trans (congrArg Result.ok shape), lastValue, finalCorrect⟩

end BulksketchBridge.FrobeniusTables
