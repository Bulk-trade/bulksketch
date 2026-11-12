import BulksketchBridge.X86FiniteAddressSpec

namespace BulksketchBridge.X86MaskedMemory

open Aeneas.Std Aeneas.Std.Avx512Register Llbc

/-- Active addresses in a numerically representable source window do not
wrap in the machine-width address space. This law does not assign pointer
provenance to an arbitrary numeric address. -/
theorem address_add_exact (base : Address) (offset : Nat) (room : base.toNat + offset < 2 ^ 64) :
    (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
  have bounded : offset < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt room]

theorem liftHeap_address (heap : AddressHeap) (base : Address) (offset : Nat)
    (room : base.toNat + offset < 2 ^ 64) :
    liftHeap heap (base.toNat + offset) = heap (base + BitVec.ofNat 64 offset) := by
  unfold liftHeap
  rw [ite_eq_left room]
  apply congrArg heap
  apply BitVec.eq_of_toNat_eq
  rw [address_add_exact base offset room, BitVec.toNat_ofNat, Nat.mod_eq_of_lt room]

theorem liftPermission_address (permit : Address → Bool) (base : Address) (offset : Nat)
    (room : base.toNat + offset < 2 ^ 64) :
    liftPermission permit (base.toNat + offset) = permit (base + BitVec.ofNat 64 offset) := by
  unfold liftPermission
  rw [decide_eq_true_eq.mpr room, Bool.true_and]
  apply congrArg permit
  apply BitVec.eq_of_toNat_eq
  rw [address_add_exact base offset room, BitVec.toNat_ofNat, Nat.mod_eq_of_lt room]

private theorem liftHeap_restrict (heap : Memory)
    (high : ∀ n, 2 ^ 64 ≤ n → heap n = none) :
    liftHeap (fun address => heap address.toNat) = heap := by
  funext address
  by_cases fit : address < 2 ^ 64
  · simp only [liftHeap, ite_eq_left fit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  · rw [liftHeap, ite_eq_right fit, high address (by omega)]

theorem llbc_load_finite_address : LlbcFiniteLoadContract := by
  intro heap base words permit admitted fits bytes
  apply llbc_load_refines words admitted (liftHeap heap) (liftPermission permit) base.toNat
  intro lane byte active
  rw [liftHeap_address]
  · exact bytes lane byte active
  · have byteBound := byte.isLt
    simp only [offsetOf]
    omega

theorem llbc_store_finite_address : LlbcFiniteStoreContract := by
  intro heap base count permit value admitted fits writable
  have permitted : ∀ offset, offset < 8 * count.val →
      ((liftHeap heap) (base.toNat + offset)).isSome = true ∧
        liftPermission permit (base.toNat + offset) = true := by
    intro offset bounded
    have fitsAddress : base.toNat + offset < 2 ^ 64 := by omega
    rw [liftHeap_address heap base offset fitsAddress, liftPermission_address permit base offset fitsAddress]
    exact writable offset bounded
  obtain ⟨mask, updated, normal, storeNormal, _, frame⟩ :=
    store_register_payload count admitted (liftHeap heap) (liftPermission permit) base.toNat value permitted
  have updatedAbove : ∀ address, 2 ^ 64 ≤ address → updated address = none := by
    intro address above
    rw [frame address (Or.inr (by omega)), liftHeap, ite_eq_right (by omega)]
  refine ⟨fun address => updated address.toNat, ?_, ?_, ?_⟩
  · rw [liftHeap_restrict updated updatedAbove, exec_store _ _ _ _ mask normal, storeNormal]
    rfl
  · intro lane byte active
    have offsetFits : base.toNat + (offsetOf lane byte).val < 2 ^ 64 := by
      have byteBound := byte.isLt
      simp only [offsetOf]
      omega
    dsimp only
    rw [address_add_exact base _ offsetFits]
    have activeMask : enabled mask.bv lane = true := by
      obtain ⟨exactMask, maskNormal, _, bits⟩ := X86LaneMask.mask_refines count admitted
      have same : exactMask = mask := Result.ok_injective (maskNormal.symm.trans normal)
      rw [← same, enabled, bits lane.val lane.isLt, decide_eq_true_eq]
      exact active
    exact stored_byte _ _ _ _ _ _ storeNormal lane byte activeMask
  · intro address outside
    dsimp only
    rw [frame address.toNat outside]
    rw [liftHeap, ite_eq_left address.isLt]
    apply congrArg heap
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt address.isLt]

private theorem lift_word_window (heap : AddressHeap) (base : Address) (count : Nat)
    (words : Nat → BitVec 64) (fits : base.toNat + 8 * count ≤ 2 ^ 64)
    (bytes : FiniteWordWindow heap base count words) :
    WordWindow (liftHeap heap) base.toNat count words := by
  intro index bounded byte
  have byteBound := byte.isLt
  rw [Nat.add_assoc, liftHeap_address heap base _ (by omega)]
  exact bytes index bounded byte

theorem llbc_xor_finite_address : LlbcFiniteXorContract := by
  intro heap left right count permit leftWords rightWords leftFits rightFits leftBytes rightBytes writable separated
  have written : WritableWindow (liftHeap heap) (liftPermission permit) left.toNat count.val := by
    intro offset bounded
    have addressBound : left.toNat + offset < 2 ^ 64 := by omega
    rw [liftHeap_address heap left offset addressBound, liftPermission_address permit left offset addressBound]
    exact writable offset bounded
  obtain ⟨updated, run, window, frame⟩ := AvxXorLlbc.xor_assign_refines (liftHeap heap)
    (liftPermission permit) ⟨left.toNat, count⟩ ⟨right.toNat, count⟩ rfl leftWords rightWords
    (lift_word_window heap left _ leftWords leftFits leftBytes)
    (lift_word_window heap right _ rightWords rightFits rightBytes) written separated
  change ∀ address, address < left.toNat ∨ left.toNat + 8 * count.val ≤ address →
    updated address = liftHeap heap address at frame
  have high : ∀ address, 2 ^ 64 ≤ address → updated address = none := by
    intro address above
    rw [frame address (Or.inr (by omega)), liftHeap, ite_eq_right (by omega)]
  refine ⟨fun address => updated address.toNat, ?_, ?_, ?_⟩
  · rw [liftHeap_restrict updated high]
    exact run
  · intro index bounded byte
    have byteBound := byte.isLt
    dsimp only
    rw [address_add_exact left _ (by omega), ← Nat.add_assoc]
    exact window index bounded byte
  · intro address outside
    dsimp only
    rw [frame address.toNat outside, liftHeap, ite_eq_left address.isLt]
    apply congrArg heap
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt address.isLt]

private theorem read_word_finite (heap : AddressHeap) (base index : Nat)
    (fits : base + 8 * (index + 1) ≤ 2 ^ 64) :
    readLane (liftHeap heap) (base + 8 * index) 0 = finiteWord heap (BitVec.ofNat 64 base) index := by
  have baseFit : base < 2 ^ 64 := by omega
  have baseValue : (BitVec.ofNat 64 base).toNat = base := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt baseFit]
  have bytes :
      (fun byte : Fin 8 => ((liftHeap heap) (base + 8 * index + (offsetOf 0 byte).val)).getD 0) =
      (fun byte : Fin 8 => (heap (BitVec.ofNat 64 base + BitVec.ofNat 64 (8 * index + byte.val))).getD 0) := by
    funext byte
    have byteBound := byte.isLt
    have fitsAddress : (BitVec.ofNat 64 base).toNat + (8 * index + byte.val) < 2 ^ 64 := by
      rw [baseValue]
      omega
    simp only [offsetOf, Fin.val_zero, Nat.mul_zero, Nat.zero_add, Nat.add_assoc]
    rw [← liftHeap_address heap (BitVec.ofNat 64 base) _ fitsAddress, baseValue]
  unfold readLane finiteWord
  rw [bytes]

theorem llbc_difference_finite_address : LlbcFiniteDifferenceContract := by
  intro inputs heap permit admitted dstFits localFits remoteFits
  obtain ⟨nonzero, updated, normal, bytes, flag, frame⟩ :=
    Difference.difference_refines inputs (liftPermission permit) (liftHeap heap) admitted
  have high : ∀ address, 2 ^ 64 ≤ address → updated address = none := by
    intro address above
    rw [frame address (Or.inr (by omega)), liftHeap, ite_eq_right (by omega)]
  have delta (index : Nat) (bounded : index < inputs.dst.len.val) :
      Difference.deltaWord inputs (liftHeap heap) index = finiteDeltaWord inputs heap index := by
    have localLen := admitted.localLength
    have remoteLen := admitted.remoteLength
    unfold Difference.deltaWord finiteDeltaWord
    rw [read_word_finite heap inputs.localWords.base index (by omega),
      read_word_finite heap inputs.remoteBytes.base index (by omega)]
  refine ⟨nonzero, fun address => updated address.toNat, ?_, ?_, ?_, ?_⟩
  · rw [liftHeap_restrict updated high]
    exact normal
  · intro index bounded byte
    have byteBound := byte.isLt
    have baseBound : inputs.dst.base < 2 ^ 64 := by omega
    have baseValue : (BitVec.ofNat 64 inputs.dst.base).toNat = inputs.dst.base := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt baseBound]
    dsimp only
    rw [address_add_exact _ _ (by rw [baseValue]; omega), baseValue, ← Nat.add_assoc, ← delta index bounded]
    exact bytes index bounded byte
  · rw [flag]
    constructor
    · rintro ⟨index, bounded, value⟩
      exact ⟨index, bounded, by simpa only [delta index bounded] using value⟩
    · rintro ⟨index, bounded, value⟩
      exact ⟨index, bounded, by simpa only [delta index bounded] using value⟩
  · intro address outside
    dsimp only
    rw [frame address.toNat outside, liftHeap, ite_eq_left address.isLt]
    apply congrArg heap
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt address.isLt]

end BulksketchBridge.X86MaskedMemory
