import BulksketchBridge.X86MaskedMemorySpec
import BulksketchBridge.X86LaneMask

namespace BulksketchBridge.X86MaskedMemory

open Aeneas.Std

theorem readCheck_iff (mem : Memory) (base : Nat) (mask : BitVec 8) :
    readCheck mem base mask = true ↔ Readable mem base mask := by
  simp only [readCheck, Readable, List.all_eq_true, List.mem_finRange, true_implies]
  constructor
  · intro valid offset active
    simpa only [ite_eq_left active] using valid offset
  · intro valid offset
    by_cases active : enabled mask (laneOf offset) = true
    · simpa only [ite_eq_left active] using valid offset active
    · simp only [ite_eq_right active]

theorem writeCheck_iff (mem : Memory) (permit : Nat → Bool) (base : Nat) (mask : BitVec 8) :
    writeCheck mem permit base mask = true ↔ Writable mem permit base mask := by
  simp only [writeCheck, Writable, List.all_eq_true, List.mem_finRange, true_implies]
  constructor
  · intro valid offset active
    simpa only [ite_eq_left active, Bool.and_eq_true] using valid offset
  · intro valid offset
    by_cases active : enabled mask (laneOf offset) = true
    · simpa only [ite_eq_left active, Bool.and_eq_true] using valid offset active
    · simp only [ite_eq_right active]

@[simp] theorem laneOf_offsetOf (lane byte : Fin 8) : laneOf (offsetOf lane byte) = lane := by
  apply Fin.ext
  simp only [laneOf, offsetOf]
  omega

@[simp] theorem byteOf_offsetOf (lane byte : Fin 8) : byteOf (offsetOf lane byte) = byte := by
  apply Fin.ext
  simp only [byteOf, offsetOf]
  omega

theorem written_at (mem : Memory) (base : Nat) (mask : BitVec 8) (value : Lanes) (offset : Fin 64) :
    writtenBytes mem base mask value (base + offset.val) =
      if enabled mask (laneOf offset) then some (wordByte (value (laneOf offset)) (byteOf offset))
      else mem (base + offset.val) := by
  have within : base ≤ base + offset.val ∧ base + offset.val < base + 64 := by omega
  simp only [writtenBytes, dite_eq_left within, Nat.add_sub_cancel_left]

theorem written_frame (mem : Memory) (base : Nat) (mask : BitVec 8) (value : Lanes) (address : Nat)
    (outside : ¬ ∃ offset : Fin 64, address = base + offset.val ∧ enabled mask (laneOf offset) = true) :
    writtenBytes mem base mask value address = mem address := by
  unfold writtenBytes
  split
  · rename_i within
    have disabled : ¬ enabled mask (laneOf ⟨address - base, by omega⟩) = true := by
      intro active
      exact outside ⟨⟨address - base, by omega⟩, by simp only; omega, active⟩
    rw [ite_eq_right disabled]
  · rfl

theorem stored_byte (mem updated : Memory) (permit : Nat → Bool) (base : Nat)
    (mask : BitVec 8) (value : Lanes) (normal : store mem permit base mask value = some updated)
    (lane byte : Fin 8) (active : enabled mask lane = true) :
    updated (base + (offsetOf lane byte).val) = some (wordByte (value lane) byte) := by
  unfold store at normal
  split at normal
  · rw [← Option.some.inj normal, written_at, laneOf_offsetOf, byteOf_offsetOf, ite_eq_left active]
  · contradiction

theorem readLane_of_bytes (mem : Memory) (base : Nat) (lane : Fin 8) (word : BitVec 64)
    (bytes : ∀ byte : Fin 8,
      mem (base + (offsetOf lane byte).val) = some (wordByte word byte)) :
    readLane mem base lane = word := by
  unfold readLane
  have same : (List.ofFn fun byte : Fin 8 => (mem (base + (offsetOf lane byte).val)).getD 0) =
      word.toLEBytes := by
    apply List.ext_getElem
    · simp
    · intro index bounded leftBound
      have inLane : index < 8 := by simpa using bounded
      rw [List.getElem_ofFn, bytes ⟨index, inLane⟩]
      simp only [Option.getD_some, wordByte]
      exact (List.Inhabited_getElem_eq_getElem! _ _ leftBound).symm
  rw [same, BitVec.fromLEBytes_toLEBytes (by decide)]
  apply BitVec.eq_of_getLsbD_eq
  intro index bounded
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_cast, bounded, decide_true, Bool.true_and]

theorem zero_mask_load (mem : Memory) (base : Nat) :
    load mem base 0 = some ((fun _ => 0), mem) := by
  have valid : Readable mem base 0 := by simp [Readable, enabled]
  rw [load, ite_eq_left ((readCheck_iff mem base 0).mpr valid)]
  simp [enabled]

theorem zero_mask_store (mem : Memory) (permit : Nat → Bool) (base : Nat) (value : Lanes) :
    store mem permit base 0 value = some mem := by
  have valid : Writable mem permit base 0 := by simp [Writable, enabled]
  rw [store, ite_eq_left ((writeCheck_iff mem permit base 0).mpr valid)]
  congr 1
  funext address
  apply written_frame
  simp [enabled]

theorem store_readback (mem : Memory) (permit : Nat → Bool) (base : Nat)
    (mask : BitVec 8) (value : Lanes) (valid : Writable mem permit base mask) :
    ∃ updated : Memory,
      store mem permit base mask value = some updated ∧
      load updated base mask = some ((fun lane => if enabled mask lane then value lane else 0), updated) ∧
      ∀ address, (¬ ∃ offset : Fin 64, address = base + offset.val ∧ enabled mask (laneOf offset) = true) →
        updated address = mem address := by
  refine ⟨writtenBytes mem base mask value, by simp [store, (writeCheck_iff _ _ _ _).mpr valid],
    ?_, written_frame mem base mask value⟩
  have readable : Readable (writtenBytes mem base mask value) base mask := by
    intro offset active
    rw [written_at, ite_eq_left active]
    rfl
  simp only [load, (readCheck_iff _ _ _).mpr readable, ite_true]
  congr 2
  funext lane
  by_cases active : enabled mask lane = true
  · simp only [active, ite_true]
    apply readLane_of_bytes
    intro byte
    rw [written_at, laneOf_offsetOf, byteOf_offsetOf, ite_eq_left active]
  · simp only [ite_eq_right active]

private theorem selected_byte (mask : BitVec 8) (len : Nat)
    (bits : ∀ lane : Nat, lane < 8 → mask.getLsbD lane = decide (lane < len)) (offset : Fin 64) :
    enabled mask (laneOf offset) = true ↔ offset.val < 8 * len := by
  rw [enabled, bits _ (laneOf offset).isLt, decide_eq_true_eq]
  simp only [laneOf]
  omega

/-- Compose the actual source mask with byte reads on the admitted slice.
The source pointer correspondence is the explicit `bytes` premise. -/
theorem source_mask_load_prefix (words : Slice U64) (admitted : words.length ≤ 8)
    (mem : Memory) (base : Nat)
    (bytes : ∀ (lane byte : Fin 8), lane.val < words.length →
      mem (base + (offsetOf lane byte).val) = some (wordByte words[lane.val]!.bv byte)) :
    ∃ mask : U8, bulksketch.backend.x86_vpclmul512.mask words.len = Aeneas.Std.Result.ok mask ∧
      load mem base mask.bv = some ((fun lane =>
        if lane.val < words.length then words[lane.val]!.bv else 0), mem) := by
  obtain ⟨mask, normal, _, bits⟩ := X86LaneMask.mask_refines words.len (by simpa using admitted)
  have laneBits (lane : Fin 8) : enabled mask.bv lane = decide (lane.val < words.length) := by
    simpa only [enabled, Slice.len_val] using bits lane.val lane.isLt
  have readable : Readable mem base mask.bv := by
    intro offset active
    have bounded : (laneOf offset).val < words.length := by
      rw [laneBits, decide_eq_true_eq] at active
      exact active
    have split : offsetOf (laneOf offset) (byteOf offset) = offset := by
      apply Fin.ext
      simp only [offsetOf, laneOf, byteOf]
      omega
    rw [← split, bytes _ _ bounded]
    rfl
  refine ⟨mask, normal, ?_⟩
  simp only [load, (readCheck_iff _ _ _).mpr readable, ite_true]
  congr 2
  funext lane
  rw [laneBits]
  by_cases bounded : lane.val < words.length
  · simp only [bounded, decide_true, ite_true]
    exact readLane_of_bytes mem base lane _ (fun byte => bytes lane byte bounded)
  · simp only [bounded, decide_false, Bool.false_eq_true, ite_false]

/-- Compose the actual source mask with checked byte writes, complete lane
readback and a frame outside the borrowed prefix. -/
theorem source_mask_store_prefix (len : Usize) (admitted : len.val ≤ 8)
    (mem : Memory) (permit : Nat → Bool) (base : Nat) (value : Lanes)
    (window : ∀ offset : Nat, offset < 8 * len.val →
      (mem (base + offset)).isSome = true ∧ permit (base + offset) = true) :
    ∃ mask : U8, ∃ updated : Memory,
      bulksketch.backend.x86_vpclmul512.mask len = Aeneas.Std.Result.ok mask ∧
      store mem permit base mask.bv value = some updated ∧
      load updated base mask.bv = some ((fun lane =>
        if lane.val < len.val then value lane else 0), updated) ∧
      ∀ address, address < base ∨ base + 8 * len.val ≤ address → updated address = mem address := by
  obtain ⟨mask, normal, _, bits⟩ := X86LaneMask.mask_refines len admitted
  have valid : Writable mem permit base mask.bv := by
    intro offset active
    exact window offset.val ((selected_byte mask.bv len.val bits offset).mp active)
  obtain ⟨updated, write, read, frame⟩ := store_readback mem permit base mask.bv value valid
  refine ⟨mask, updated, normal, write, ?_, ?_⟩
  · rw [read]
    congr 2
    funext lane
    rw [enabled, bits lane.val lane.isLt]
    simp
  · intro address outside
    apply frame address
    rintro ⟨offset, rfl, active⟩
    have selected := (selected_byte mask.bv len.val bits offset).mp active
    omega

end BulksketchBridge.X86MaskedMemory
