import BulksketchBridge.X86MaskedMemoryLlbc

namespace BulksketchBridge.X86MaskedMemory

open Aeneas.Std Aeneas.Std.Avx512Register

/-- Representation of a contiguous little-endian word view in the heap. -/
def WordWindow (heap : Memory) (base count : Nat) (words : Nat → BitVec 64) : Prop :=
  ∀ index : Nat, index < count → ∀ byte : Fin 8,
    heap (base + 8 * index + byte.val) = some (wordByte (words index) byte)

def WritableWindow (heap : Memory) (permit : Nat → Bool) (base count : Nat) : Prop :=
  ∀ offset : Nat, offset < 8 * count →
    (heap (base + offset)).isSome = true ∧ permit (base + offset) = true

theorem load_mapped_window (view : Llbc.SliceView) (admitted : view.len.val ≤ 8)
    (heap : Memory) (permit : Nat → Bool)
    (mapped : ∀ offset : Nat, offset < 8 * view.len.val →
      (heap (view.base + offset)).isSome = true) :
    Llbc.exec permit Llbc.loadProgram (Llbc.loadInput heap view) =
      some (.register (unflatten fun lane =>
        if lane.val < view.len.val then readLane heap view.base lane else 0), heap) := by
  obtain ⟨mask, normal, _, bits⟩ := X86LaneMask.mask_refines view.len admitted
  rw [Llbc.exec_load _ _ _ mask normal]
  have active (lane : Fin 8) : enabled mask.bv lane = decide (lane.val < view.len.val) :=
    bits lane.val lane.isLt
  have readable : Readable heap view.base mask.bv := by
    intro offset selected
    rw [active, decide_eq_true_eq] at selected
    apply mapped
    simp only [laneOf] at selected
    omega
  simp [load, (readCheck_iff _ _ _).mpr readable, active]

theorem load_window (view : Llbc.SliceView) (admitted : view.len.val ≤ 8)
    (heap : Memory) (permit : Nat → Bool) (words : Nat → BitVec 64)
    (bytes : WordWindow heap view.base view.len.val words) :
    Llbc.exec permit Llbc.loadProgram (Llbc.loadInput heap view) =
      some (.register (unflatten fun lane =>
        if lane.val < view.len.val then words lane.val else 0), heap) := by
  obtain ⟨mask, normal, _, bits⟩ := X86LaneMask.mask_refines view.len admitted
  rw [Llbc.exec_load _ _ _ mask normal]
  have active (lane : Fin 8) : enabled mask.bv lane = decide (lane.val < view.len.val) :=
    bits lane.val lane.isLt
  have readable : Readable heap view.base mask.bv := by
    intro offset selected
    rw [active, decide_eq_true_eq] at selected
    have address : view.base + offset.val =
        view.base + 8 * (laneOf offset).val + (byteOf offset).val := by
      simp only [laneOf, byteOf]
      omega
    rw [address, bytes _ selected _]
    rfl
  simp only [load, (readCheck_iff _ _ _).mpr readable, ite_true, Option.map_some]
  congr 3
  apply congrArg unflatten
  funext lane
  rw [active]
  by_cases bounded : lane.val < view.len.val
  · simp only [bounded, decide_true, ite_true]
    apply readLane_of_bytes
    intro byte
    simpa only [offsetOf, ← Nat.add_assoc] using bytes lane.val bounded byte
  · simp [bounded]

theorem store_window (view : Llbc.SliceView) (admitted : view.len.val ≤ 8)
    (heap : Memory) (permit : Nat → Bool) (value : Word512)
    (writable : WritableWindow heap permit view.base view.len.val) :
    ∃ updated : Memory,
      Llbc.exec permit Llbc.storeProgram (Llbc.storeInput heap view value) =
        some (.unit, updated) ∧
      WordWindow updated view.base view.len.val
        (fun index => if inside : index < 8 then flatten value ⟨index, inside⟩ else 0) ∧
      ∀ address, address < view.base ∨ view.base + 8 * view.len.val ≤ address →
        updated address = heap address := by
  obtain ⟨mask, updated, normal, write, _, frame⟩ :=
    source_mask_store_prefix view.len admitted heap permit view.base (flatten value) writable
  obtain ⟨provedMask, provedNormal, _, bits⟩ := X86LaneMask.mask_refines view.len admitted
  have same : mask = provedMask := Result.ok_injective (normal.symm.trans provedNormal)
  subst provedMask
  refine ⟨updated, ?_, ?_, frame⟩
  · rw [Llbc.exec_store _ _ _ _ mask normal, write]
    rfl
  · intro index inside byte
    have bounded : index < 8 := by omega
    simp only [dite_eq_left bounded]
    have lane : enabled mask.bv ⟨index, bounded⟩ = true := by
      rw [enabled, bits index bounded, decide_eq_true_eq]
      exact inside
    simpa only [offsetOf, ← Nat.add_assoc] using
      stored_byte heap updated permit view.base mask.bv (flatten value) write ⟨index, bounded⟩ byte lane

end BulksketchBridge.X86MaskedMemory
