import BulksketchBridge.X86AllocationSpec
import BulksketchBridge.X86FiniteAddress

namespace BulksketchBridge.X86MaskedMemory.Allocation

open Aeneas.Std Aeneas.Std.Avx512Register Llbc

theorem ReadView.no_wrap {live la57 heap base length alignment}
    (view : ReadView live la57 heap base length alignment) :
    base.toNat + length ≤ 2 ^ 64 := by
  by_cases nonempty : 0 < length
  · obtain ⟨_, _, _, extent, _, contained⟩ := view.allocated nonempty
    exact contained.trans extent.noWrap
  · have empty : length = 0 := by omega
    simpa only [empty, Nat.add_zero] using Nat.le_of_lt base.isLt

private theorem Extent.inside_canonical {la57 first size}
    (extent : Extent la57 first size) (address : Address)
    (inside : first.toNat ≤ address.toNat ∧ address.toNat < first.toNat + size) :
    Canonical la57 address := by
  rcases extent.canonical with low | high
  · exact Or.inl (inside.2.trans_le low)
  · exact Or.inr (high.trans inside.1)

private theorem separated {destination dstLength source srcLength}
    (apart : Disjoint destination dstLength source srcLength) (byte : Nat) (bounded : byte < srcLength) :
    source.toNat + byte < destination.toNat ∨ destination.toNat + dstLength ≤ source.toNat + byte := by
  by_cases before : source.toNat + byte < destination.toNat
  · exact Or.inl before
  · refine Or.inr (Nat.le_of_not_gt ?_)
    intro overlaps
    exact apart (source.toNat + byte) (by omega) overlaps (by omega) (by omega)

theorem allocated_mask_footprint : ActualAllocatedMaskFootprint := by
  intro live la57 heap base length alignment start count view bounded chunkRoom
  obtain ⟨mask, normal, _, bits⟩ := X86LaneMask.mask_refines count bounded
  have activeByte (byte : Fin 64) :
      enabled mask.bv (laneOf byte) = decide (byte.val < 8 * count.val) := by
    rw [enabled, bits _ (laneOf byte).isLt]
    apply decide_eq_decide.mpr
    change byte.val / 8 < count.val ↔ byte.val < 8 * count.val
    omega
  refine ⟨mask, normal, activeByte, ?_⟩
  intro nonempty
  obtain ⟨first, size, inLive, extent, firstBound, contained⟩ := view.allocated (by omega)
  refine ⟨first, size, inLive, ?_⟩
  intro byte enabledByte
  rw [activeByte, decide_eq_true_eq] at enabledByte
  have byteRoom : start + byte.val < length := by omega
  have noWrap := view.no_wrap
  let chunk := base + BitVec.ofNat 64 start
  let address := chunk + BitVec.ofNat 64 byte.val
  have chunkValue : chunk.toNat = base.toNat + start := address_add_exact base start (by omega)
  have addressValue : address.toNat = base.toNat + start + byte.val := by
    change (chunk + _).toNat = _
    rw [address_add_exact _ _ (by rw [chunkValue]; omega), chunkValue]
  have same : address = base + BitVec.ofNat 64 (start + byte.val) := by
    apply BitVec.eq_of_toNat_eq
    rw [addressValue, address_add_exact _ _ (by omega), Nat.add_assoc]
  have inside : first.toNat ≤ address.toNat ∧ address.toNat < first.toNat + size := by
    rw [addressValue]
    omega
  have objectBound := extent.sizeBound
  refine ⟨addressValue, by omega, inside.1, inside.2, extent.inside_canonical address inside, ?_⟩
  change (heap address).isSome = true
  rw [same]
  exact view.initialized _ byteRoom

theorem allocated_load_refines : AllocatedLoadContract := by
  intro live la57 heap base words permit admitted view bytes
  exact llbc_load_finite_address heap base words permit admitted view.no_wrap
    (fun lane byte active => bytes lane.val active byte)

theorem allocated_store_refines : AllocatedStoreContract := by
  intro live la57 heap base count permit value admitted view
  exact llbc_store_finite_address heap base count permit value admitted view.toReadView.no_wrap
    (fun offset active => ⟨view.initialized offset active, view.exclusive offset active⟩)

theorem allocated_xor_refines : AllocatedXorContract := by
  intro live la57 heap left right count permit leftWords rightWords dst src apart leftBytes rightBytes
  exact llbc_xor_finite_address heap left right count permit leftWords rightWords
    dst.toReadView.no_wrap src.no_wrap leftBytes rightBytes
    (fun offset active => ⟨dst.initialized offset active, dst.exclusive offset active⟩) (separated apart)

private theorem view_mapped {live la57 heap base length alignment}
    (view : ReadView live la57 heap base length alignment) :
    Difference.MappedBytes (liftHeap heap) base.toNat length := by
  intro offset active
  have room := view.no_wrap
  rw [liftHeap_address _ _ _ (by omega)]
  exact view.initialized offset active

theorem allocated_difference_refines : AllocatedDifferenceContract := by
  intro live la57 heap destination localWords remoteBytes count remoteCount permit lengths
    dst localView remoteView localApart remoteApart
  let inputs := differenceInputs destination localWords remoteBytes count remoteCount
  have dstFits := dst.toReadView.no_wrap
  have admitted : Difference.Admitted inputs (liftPermission permit) (liftHeap heap) := by
    refine ⟨rfl, lengths, view_mapped localView, view_mapped remoteView, ?_,
      separated localApart, separated remoteApart⟩
    intro offset active
    change offset < 8 * count.val at active
    change ((liftHeap heap) (destination.toNat + offset)).isSome = true ∧
      liftPermission permit (destination.toNat + offset) = true
    have fits : destination.toNat + offset < 2 ^ 64 := by omega
    rw [liftHeap_address _ _ _ fits, liftPermission_address _ _ _ fits]
    exact ⟨dst.initialized offset active, dst.exclusive offset active⟩
  obtain ⟨flag, updated, run, words, flagEq, frame⟩ :=
    llbc_difference_finite_address inputs heap permit admitted dstFits localView.no_wrap remoteView.no_wrap
  have sameBase : BitVec.ofNat 64 inputs.dst.base = destination := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 64 destination.toNat).toNat = destination.toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destination.isLt]
  rw [sameBase] at words
  exact ⟨flag, updated, run, words, flagEq, frame⟩

end BulksketchBridge.X86MaskedMemory.Allocation
