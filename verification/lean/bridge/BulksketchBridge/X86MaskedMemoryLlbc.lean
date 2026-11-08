import BulksketchBridge.X86MaskedMemoryLlbcGenerated

namespace BulksketchBridge.X86MaskedMemory.Llbc

open Aeneas.Std Aeneas.Std.Avx512Register

set_option maxHeartbeats 150000

/-- Normal-path execution of the original load LLBC. The only input pointer
value is the borrowed slice view, whose metadata comes from `words.len`. -/
theorem exec_load (heap : Memory) (permit : Nat → Bool) (words : SliceView)
    (mask : U8) (normal : bulksketch.backend.x86_vpclmul512.mask words.len = .ok mask) :
    exec permit loadProgram (loadInput heap words) =
      (X86MaskedMemory.load heap words.base mask.bv).map
        (fun (value, heap) => (.register (unflatten value), heap)) := by
  cases access : X86MaskedMemory.load heap words.base mask.bv with
  | none => simp [loadProgram, exec, step, init, read, move, writeLocal, loadInput, normal, access]
  | some result =>
    rcases result with ⟨value, heap'⟩
    simp [loadProgram, exec, step, init, read, move, writeLocal, loadInput, normal, access]

/-- Normal-path execution of the original store LLBC. Its Rust return slot
contains Unit and the destination data is in the heap returned to the caller. -/
theorem exec_store (heap : Memory) (permit : Nat → Bool) (words : SliceView) (value : Word512)
    (mask : U8) (normal : bulksketch.backend.x86_vpclmul512.mask words.len = .ok mask) :
    exec permit storeProgram (storeInput heap words value) =
      (X86MaskedMemory.store heap permit words.base mask.bv (flatten value)).map
        (fun heap => (.unit, heap)) := by
  cases access : X86MaskedMemory.store heap permit words.base mask.bv (flatten value) <;>
    simp [storeProgram, exec, step, init, read, move, writeLocal, storeInput, normal, access]

def LlbcLoadContract : Prop :=
  ∀ (words : Slice U64) (_admitted : words.length ≤ 8)
    (heap : Memory) (permit : Nat → Bool) (base : Nat),
    (∀ (lane byte : Fin 8), lane.val < words.length →
      heap (base + (offsetOf lane byte).val) = some (wordByte words[lane.val]!.bv byte)) →
    exec permit loadProgram (loadInput heap ⟨base, words.len⟩) =
      some (.register (unflatten fun lane =>
        if lane.val < words.length then words[lane.val]!.bv else 0), heap)

theorem llbc_load_refines : LlbcLoadContract := by
  intro words admitted heap permit base bytes
  obtain ⟨mask, normal, load⟩ := source_mask_load_prefix words admitted heap base bytes
  rw [exec_load _ _ _ mask normal]
  simp only [load, Option.map_some]

def LlbcStoreContract : Prop :=
  ∀ (view : SliceView) (admitted : view.len.val ≤ 8) (heap : Memory)
    (permit : Nat → Bool) (value : Word512),
    (∀ offset : Nat, offset < 8 * view.len.val →
      (heap (view.base + offset)).isSome = true ∧ permit (view.base + offset) = true) →
    ∃ updated : Memory,
      exec permit storeProgram (storeInput heap view value) = some (.unit, updated) ∧
      readPayload updated view.base view.len.val admitted =
        registerPayload value view.len.val admitted ∧
      ∀ address, address < view.base ∨ view.base + 8 * view.len.val ≤ address →
        updated address = heap address

theorem llbc_store_refines : LlbcStoreContract := by
  intro view admitted heap permit value window
  obtain ⟨mask, updated, normal, store, payload, frame⟩ :=
    store_register_payload view.len admitted heap permit view.base value window
  refine ⟨updated, ?_, payload, frame⟩
  rw [exec_store _ _ _ _ mask normal]
  simp only [store, Option.map_some]

end BulksketchBridge.X86MaskedMemory.Llbc
