import BulksketchBridge.X86DifferenceStep

namespace BulksketchBridge.X86MaskedMemory.Difference

open Aeneas.Std Aeneas.Std.Avx512Register

structure Admitted (inputs : Inputs) (permit : Nat → Bool) (heap : Memory) : Prop where
  localLength : inputs.localWords.len.val = inputs.dst.len.val
  remoteLength : inputs.remoteBytes.len.val = 8 * inputs.dst.len.val
  localMapped : MappedBytes heap inputs.localWords.base (8 * inputs.localWords.len.val)
  remoteMapped : MappedBytes heap inputs.remoteBytes.base inputs.remoteBytes.len.val
  destination : WritableWindow heap permit inputs.dst.base inputs.dst.len.val
  localSeparated : ∀ byte, byte < 8 * inputs.localWords.len.val →
    inputs.localWords.base + byte < inputs.dst.base ∨
      inputs.dst.base + 8 * inputs.dst.len.val ≤ inputs.localWords.base + byte
  remoteSeparated : ∀ byte, byte < inputs.remoteBytes.len.val →
    inputs.remoteBytes.base + byte < inputs.dst.base ∨
      inputs.dst.base + 8 * inputs.dst.len.val ≤ inputs.remoteBytes.base + byte

structure Invariant (inputs : Inputs) (initial : Memory) (done : Nat) (state : State) : Prop where
  words : WordWindow state.heap inputs.dst.base done (deltaWord inputs initial)
  frame : ∀ address, address < inputs.dst.base ∨ inputs.dst.base + 8 * done ≤ address →
    state.heap address = initial address
  flag : testSelfNonzero state.any = true ↔ ∃ index, index < done ∧ deltaWord inputs initial index ≠ 0

private theorem flag_nonzero (value : Word512) :
    testSelfNonzero value = true ↔ ∃ lane : Fin 8, flatten value lane ≠ 0 := by
  simp only [testSelfNonzero, List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq]

private theorem flag_or (a b : Word512) :
    testSelfNonzero (orValue a b) = true ↔ testSelfNonzero a = true ∨ testSelfNonzero b = true := by
  rw [flag_nonzero, flag_nonzero, flag_nonzero]
  constructor
  · rintro ⟨lane, nonzero⟩
    change flatten a lane ||| flatten b lane ≠ 0 at nonzero
    by_cases first : flatten a lane = 0
    · right
      refine ⟨lane, fun second => nonzero ?_⟩
      exact BitVec.or_eq_zero_iff.mpr ⟨first, second⟩
    · exact Or.inl ⟨lane, first⟩
  · rintro (⟨lane, first⟩ | ⟨lane, second⟩)
    · refine ⟨lane, ?_⟩
      change flatten a lane ||| flatten b lane ≠ 0
      exact fun zero => first (BitVec.or_eq_zero_iff.mp zero).1
    · refine ⟨lane, ?_⟩
      change flatten a lane ||| flatten b lane ≠ 0
      exact fun zero => second (BitVec.or_eq_zero_iff.mp zero).2

private theorem block_flag (inputs : Inputs) (heap : Memory) (offset : Nat) :
    testSelfNonzero (deltaRegister inputs heap offset) = true ↔
      ∃ index, offset ≤ index ∧ index < offset + width inputs offset ∧ deltaWord inputs heap index ≠ 0 := by
  rw [flag_nonzero]
  constructor
  · rintro ⟨lane, nonzero⟩
    simp only [deltaRegister, flatten_unflatten] at nonzero
    by_cases active : lane.val < width inputs offset
    · exact ⟨offset + lane.val, by omega, by omega, by simpa only [active, ite_true] using nonzero⟩
    · exact (nonzero (by simp [active])).elim
  · rintro ⟨index, lower, upper, mismatch⟩
    have nBound : width inputs offset ≤ 8 := Nat.min_le_right _ _
    have lane : index - offset < width inputs offset := by omega
    refine ⟨⟨index - offset, by omega⟩, ?_⟩
    simp only [deltaRegister, flatten_unflatten, lane, ite_true,
      show offset + (index - offset) = index by omega]
    exact mismatch

private theorem read_congr (heap initial : Memory) (base : Nat)
    (same : ∀ byte : Fin 8, heap (base + byte.val) = initial (base + byte.val)) :
    readLane heap base 0 = readLane initial base 0 := by
  unfold readLane
  congr 2
  apply congrArg List.ofFn
  funext byte
  simp only [offsetOf, Fin.val_zero, Nat.mul_zero, Nat.zero_add, same]

private theorem step_invariant (inputs : Inputs) (permit : Nat → Bool) (initial : Memory)
    (admitted : Admitted inputs permit initial) (offset : Nat) (state : State)
    (active : offset < inputs.dst.len.val) (inv : Invariant inputs initial offset state) :
    ∃ next, differenceStep inputs permit offset state = some next ∧
      Invariant inputs initial (offset + width inputs offset) next := by
  let n := width inputs offset
  have endBound : offset + n ≤ inputs.dst.len.val := by
    have := Nat.min_le_left (inputs.dst.len.val - offset) 8
    dsimp only [n, width]
    omega
  have localLength := admitted.localLength
  have remoteLength := admitted.remoteLength
  have localSame (byte : Nat) (bounded : byte < 8 * inputs.localWords.len.val) :
      state.heap (inputs.localWords.base + byte) = initial (inputs.localWords.base + byte) := by
    apply inv.frame
    rcases admitted.localSeparated byte bounded with before | after
    · exact Or.inl before
    · exact Or.inr (by omega)
  have remoteSame (byte : Nat) (bounded : byte < inputs.remoteBytes.len.val) :
      state.heap (inputs.remoteBytes.base + byte) = initial (inputs.remoteBytes.base + byte) := by
    apply inv.frame
    rcases admitted.remoteSeparated byte bounded with before | after
    · exact Or.inl before
    · exact Or.inr (by omega)
  have deltaSame (index : Nat) (bounded : index < inputs.dst.len.val) :
      deltaWord inputs state.heap index = deltaWord inputs initial index := by
    unfold deltaWord
    congr 1
    · apply read_congr
      intro byte
      rw [Nat.add_assoc]
      exact localSame _ (by have := byte.isLt; omega)
    · apply read_congr
      intro byte
      rw [Nat.add_assoc]
      exact remoteSame _ (by have := byte.isLt; omega)
  have registerSame : deltaRegister inputs state.heap offset = deltaRegister inputs initial offset := by
    unfold deltaRegister
    apply congrArg unflatten
    funext lane
    split
    · apply deltaSame
      change lane.val < n at *
      omega
    · rfl
  have localWindow : MappedBytes state.heap (inputs.localWords.base + 8 * offset) (8 * n) := by
    intro byte bounded
    rw [Nat.add_assoc, localSame _ (by omega)]
    exact admitted.localMapped _ (by omega)
  have remoteWindow : MappedBytes state.heap (inputs.remoteBytes.base + 8 * offset) (8 * n) := by
    intro byte bounded
    rw [Nat.add_assoc, remoteSame _ (by omega)]
    exact admitted.remoteMapped _ (by omega)
  have dstWindow : WritableWindow state.heap permit (inputs.dst.base + 8 * offset) n := by
    intro byte bounded
    rw [inv.frame _ (Or.inr (by omega)), Nat.add_assoc]
    exact admitted.destination _ (by omega)
  obtain ⟨updated, normal, payload, writtenFrame⟩ :=
    step_refines inputs permit offset state active localLength remoteLength localWindow remoteWindow dstWindow
  rw [registerSame] at normal
  refine ⟨_, normal, ⟨?_, ?_, ?_⟩⟩
  · intro index bounded byte
    change updated (inputs.dst.base + 8 * index + byte.val) = _
    by_cases before : index < offset
    · rw [writtenFrame _ (Or.inl (by have := byte.isLt; omega))]
      exact inv.words index before byte
    · have lane : index - offset < n := by omega
      have written := payload (index - offset) lane byte
      dsimp only at written
      rw [show inputs.dst.base + 8 * offset + 8 * (index - offset) + byte.val =
          inputs.dst.base + 8 * index + byte.val by omega,
        show offset + (index - offset) = index by omega, deltaSame _ (by omega)] at written
      exact written
  · intro address outside
    exact (writtenFrame address (by omega)).trans (inv.frame address (by omega))
  · simp only [flag_or, inv.flag, block_flag]
    constructor
    · rintro (⟨i, bound, nz⟩ | ⟨i, lower, upper, nz⟩)
      · exact ⟨i, by omega, nz⟩
      · exact ⟨i, upper, nz⟩
    · rintro ⟨i, bound, nz⟩
      by_cases earlier : i < offset
      · exact Or.inl ⟨i, earlier, nz⟩
      · exact Or.inr ⟨i, by omega, bound, nz⟩

private theorem run_invariant (inputs : Inputs) (permit : Nat → Bool) (initial : Memory)
    (admitted : Admitted inputs permit initial) (offset fuel : Nat) (state : State)
    (bounded : offset ≤ inputs.dst.len.val) (enough : inputs.dst.len.val - offset < fuel)
    (inv : Invariant inputs initial offset state) :
    ∃ final, run (differenceStep inputs permit) ⟨offset, inputs.dst.len.val, 8⟩ fuel state =
      some final ∧ Invariant inputs initial inputs.dst.len.val final := by
  induction fuel generalizing offset state with
  | zero => omega
  | succ fuel ih =>
    by_cases active : offset < inputs.dst.len.val
    · obtain ⟨next, executed, nextInv⟩ := step_invariant inputs permit initial admitted offset state active inv
      have advance : min (offset + 8) inputs.dst.len.val = offset + width inputs offset := by
        unfold width
        omega
      have progress : 0 < width inputs offset := by unfold width; omega
      have bounded' : offset + width inputs offset ≤ inputs.dst.len.val := by unfold width; omega
      obtain ⟨final, runDone, finalInv⟩ := ih (offset + width inputs offset) next bounded' (by omega) nextInv
      refine ⟨final, ?_, finalInv⟩
      simp only [run, active, ite_true, executed, advance]
      exact runDone
    · have terminal : offset = inputs.dst.len.val := by omega
      refine ⟨state, ?_, terminal ▸ inv⟩
      simp only [run, active, ite_false]

/-- Exact stateful execution of the source-pinned AVX difference caller.
Destination words are the little-endian XOR difference, the result says
whether any word differs, and all bytes outside the destination are framed. -/
def DifferenceContract : Prop :=
  ∀ inputs permit initial, Admitted inputs permit initial →
    ∃ result updated,
      differenceProgram inputs permit initial = some (result, updated) ∧
      WordWindow updated inputs.dst.base inputs.dst.len.val (deltaWord inputs initial) ∧
      (result = true ↔ ∃ index, index < inputs.dst.len.val ∧ deltaWord inputs initial index ≠ 0) ∧
      ∀ address, address < inputs.dst.base ∨ inputs.dst.base + 8 * inputs.dst.len.val ≤ address →
        updated address = initial address

theorem difference_refines : DifferenceContract := by
  intro inputs permit initial admitted
  let state : State := ⟨initial, zeroRegister⟩
  have initialInv : Invariant inputs initial 0 state := by
    refine ⟨?_, fun _ _ => rfl, ?_⟩
    · intro index impossible
      omega
    · rw [flag_nonzero]
      simp [state, zeroRegister, flatten]
  obtain ⟨final, normal, inv⟩ := run_invariant inputs permit initial admitted 0
    (inputs.dst.len.val + 1) state (Nat.zero_le _) (by omega) initialInv
  refine ⟨testSelfNonzero final.any, final.heap, ?_, inv.words, inv.flag, inv.frame⟩
  simp only [differenceProgram, differenceSetup]
  dsimp! only
  change (run (differenceStep inputs permit) ⟨0, inputs.dst.len.val, 8⟩
    (inputs.dst.len.val + 1) state).bind _ = _
  rw [normal]
  rfl

end BulksketchBridge.X86MaskedMemory.Difference
