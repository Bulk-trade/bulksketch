import BulksketchBridge.X86FiniteAddressSpec

namespace BulksketchBridge.X86MaskedMemory.Allocation

open Aeneas.Std Aeneas.Std.Avx512Register Llbc

/-- The trusted allocation metadata supplied at the Rust/heap boundary.
Each entry records the base and byte length of a live allocation. -/
abbrev LiveAllocations := Address → Nat → Prop

def canonicalHalf (la57 : Bool) : Nat := if la57 then 2 ^ 56 else 2 ^ 47

def Canonical (la57 : Bool) (address : Address) : Prop :=
  address.toNat < canonicalHalf la57 ∨ 2 ^ 64 - canonicalHalf la57 ≤ address.toNat

/-- A live allocation occupies one canonical half and has a non-wrapping
extent of at most the x86 Rust isize::MAX byte bound. -/
structure Extent (la57 : Bool) (first : Address) (size : Nat) : Prop where
  sizeBound : size ≤ 2 ^ 63 - 1
  noWrap : first.toNat + size ≤ 2 ^ 64
  canonical :
    first.toNat + size ≤ canonicalHalf la57 ∨ 2 ^ 64 - canonicalHalf la57 ≤ first.toNat

/-- Explicit slice premises at the allocation boundary. A zero-length
borrow has a nonnull aligned base and needs no allocation witness. -/
structure ReadView (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (base : Address) (length alignment : Nat) : Prop where
  nonnull : base ≠ 0
  aligned : base.toNat % alignment = 0
  allocated : 0 < length →
    ∃ first size, live first size ∧ Extent la57 first size ∧
      first.toNat ≤ base.toNat ∧ base.toNat + length ≤ first.toNat + size
  initialized : ∀ offset, offset < length →
    (heap (base + BitVec.ofNat 64 offset)).isSome = true

structure WriteView (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (permit : Address → Bool) (base : Address) (length alignment : Nat) : Prop
    extends ReadView live la57 heap base length alignment where
  exclusive : ∀ offset, offset < length → permit (base + BitVec.ofNat 64 offset) = true

/-- The admitted destination and shared view cannot overlap in their
actual byte ranges. Empty views impose no separation constraint. -/
def Disjoint (destination : Address) (dstLength : Nat) (source : Address) (srcLength : Nat) : Prop :=
  ∀ address, destination.toNat ≤ address → address < destination.toNat + dstLength →
    source.toNat ≤ address → address < source.toNat + srcLength → False

/-- The original source mask selects exactly the bytes of an admitted
chunk. Each active effective address is canonical, initialized, within the signed pointer offset bound,
and in the one live allocation that backs its borrowed view. -/
def ActualAllocatedMaskFootprint : Prop :=
  ∀ (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap) (base : Address)
    (length alignment start : Nat) (count : Usize),
    ReadView live la57 heap base length alignment →
    count.val ≤ 8 → start + 8 * count.val ≤ length →
    ∃ mask : U8, bulksketch.backend.x86_vpclmul512.mask count = Result.ok mask ∧
      (∀ byte : Fin 64, enabled mask.bv (laneOf byte) = decide (byte.val < 8 * count.val)) ∧
      (0 < count.val → ∃ first size, live first size ∧
        ∀ byte : Fin 64, enabled mask.bv (laneOf byte) = true →
          let address := (base + BitVec.ofNat 64 start) + BitVec.ofNat 64 byte.val
          address.toNat = base.toNat + start + byte.val ∧
          start + byte.val ≤ 2 ^ 63 - 1 ∧
          first.toNat ≤ address.toNat ∧ address.toNat < first.toNat + size ∧
          Canonical la57 address ∧ (heap address).isSome = true)

def AllocatedLoadContract : Prop :=
  ∀ (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap) (base : Address) (words : Slice U64)
    (permit : Address → Bool),
    words.length ≤ 8 → ReadView live la57 heap base (8 * words.length) 8 →
    FiniteWordWindow heap base words.length (fun index => words[index]!.bv) →
    exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨base.toNat, words.len⟩) =
      some (.register (unflatten fun lane =>
        if lane.val < words.length then words[lane.val]!.bv else 0), liftHeap heap)

def AllocatedStoreContract : Prop :=
  ∀ (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap) (base : Address) (count : Usize)
    (permit : Address → Bool) (value : Word512),
    count.val ≤ 8 → WriteView live la57 heap permit base (8 * count.val) 8 →
    ∃ updated : AddressHeap,
      exec (liftPermission permit) storeProgram (storeInput (liftHeap heap) ⟨base.toNat, count⟩ value) =
        some (.unit, liftHeap updated) ∧
      (∀ lane byte : Fin 8, lane.val < count.val →
        updated (base + BitVec.ofNat 64 (offsetOf lane byte).val) =
          some (wordByte (flatten value lane) byte)) ∧
      (∀ address, address.toNat < base.toNat ∨ base.toNat + 8 * count.val ≤ address.toNat →
        updated address = heap address)

def AllocatedXorContract : Prop :=
  ∀ (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap) (left right : Address)
    (count : Usize) (permit : Address → Bool) (leftWords rightWords : Nat → BitVec 64),
    WriteView live la57 heap permit left (8 * count.val) 8 →
    ReadView live la57 heap right (8 * count.val) 8 →
    Disjoint left (8 * count.val) right (8 * count.val) →
    FiniteWordWindow heap left count.val leftWords → FiniteWordWindow heap right count.val rightWords →
    ∃ updated : AddressHeap,
      AvxXorLlbc.run AvxXorLlbc.program (liftPermission permit)
        ⟨left.toNat, count⟩ ⟨right.toNat, count⟩ (liftHeap heap) = some (liftHeap updated) ∧
      FiniteWordWindow updated left count.val (fun i => leftWords i ^^^ rightWords i) ∧
      ∀ address, address.toNat < left.toNat ∨ left.toNat + 8 * count.val ≤ address.toNat →
        updated address = heap address

def differenceInputs (destination localWords remoteBytes : Address) (count remoteCount : Usize) :
    Difference.Inputs :=
  ⟨⟨destination.toNat, count⟩, ⟨localWords.toNat, count⟩, ⟨remoteBytes.toNat, remoteCount⟩⟩

/-- The original difference LLBC admits byte-aligned remote input, including
a tail shorter than one vector. The destination must be disjoint from both
shared views. The two shared views may overlap. -/
def AllocatedDifferenceContract : Prop :=
  ∀ (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (destination localWords remoteBytes : Address) (count remoteCount : Usize) (permit : Address → Bool),
    remoteCount.val = 8 * count.val →
    WriteView live la57 heap permit destination (8 * count.val) 8 →
    ReadView live la57 heap localWords (8 * count.val) 8 →
    ReadView live la57 heap remoteBytes remoteCount.val 1 →
    Disjoint destination (8 * count.val) localWords (8 * count.val) →
    Disjoint destination (8 * count.val) remoteBytes remoteCount.val →
    let inputs := differenceInputs destination localWords remoteBytes count remoteCount
    ∃ (nonzero : Bool) (updated : AddressHeap),
      Difference.differenceProgram inputs (liftPermission permit) (liftHeap heap) = some (nonzero, liftHeap updated) ∧
      FiniteWordWindow updated destination count.val (finiteDeltaWord inputs heap) ∧
      (nonzero = true ↔ ∃ index, index < count.val ∧ finiteDeltaWord inputs heap index ≠ 0) ∧
      ∀ address, address.toNat < destination.toNat ∨ destination.toNat + 8 * count.val ≤ address.toNat →
        updated address = heap address

end BulksketchBridge.X86MaskedMemory.Allocation
