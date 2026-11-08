import BulksketchBridge.AvxXorLlbc
import BulksketchBridge.X86Difference

namespace BulksketchBridge.X86MaskedMemory

open Aeneas.Std Aeneas.Std.Avx512Register Llbc

abbrev Address := BitVec 64
abbrev AddressHeap := Address → Option (BitVec 8)

def liftHeap (heap : AddressHeap) : Memory :=
  fun address => if address < 2 ^ 64 then heap (BitVec.ofNat 64 address) else none

def liftPermission (permit : Address → Bool) (address : Nat) : Bool :=
  decide (address < 2 ^ 64) && permit (BitVec.ofNat 64 address)

def FiniteWordWindow (heap : AddressHeap) (base : Address) (count : Nat)
    (words : Nat → BitVec 64) : Prop :=
  ∀ index, index < count → ∀ byte : Fin 8,
    heap (base + BitVec.ofNat 64 (8 * index + byte.val)) = some (wordByte (words index) byte)

def finiteWord (heap : AddressHeap) (base : Address) (index : Nat) : BitVec 64 :=
  (BitVec.fromLEBytes (List.ofFn fun byte : Fin 8 =>
    (heap (base + BitVec.ofNat 64 (8 * index + byte.val))).getD 0)).setWidth 64

def finiteDeltaWord (inputs : Difference.Inputs) (heap : AddressHeap) (index : Nat) : BitVec 64 :=
  finiteWord heap (BitVec.ofNat 64 inputs.localWords.base) index ^^^
  finiteWord heap (BitVec.ofNat 64 inputs.remoteBytes.base) index

/-- Observe the unchanged original masked-load LLBC in a finite-width
address heap. Active bytes are read at exactly the computed x86 offsets. -/
def LlbcFiniteLoadContract : Prop :=
  ∀ (heap : AddressHeap) (base : Address) (words : Slice U64)
    (permit : Address → Bool) (_admitted : words.length ≤ 8)
    (_fits : base.toNat + 8 * words.length ≤ 2 ^ 64)
    (_bytes : ∀ lane byte : Fin 8, lane.val < words.length →
      heap (base + BitVec.ofNat 64 (offsetOf lane byte).val) = some (wordByte words[lane.val]!.bv byte)),
      exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨base.toNat, words.len⟩) =
      some (.register (unflatten fun lane =>
        if lane.val < words.length then words[lane.val]!.bv else 0), liftHeap heap)

/-- The unchanged original masked-store LLBC returns a finite-width heap.
It updates exactly the active lane bytes and preserves the finite frame. -/
def LlbcFiniteStoreContract : Prop :=
  ∀ (heap : AddressHeap) (base : Address) (count : Usize)
    (permit : Address → Bool) (value : Word512) (_admitted : count.val ≤ 8)
    (_fits : base.toNat + 8 * count.val ≤ 2 ^ 64)
    (_writable : ∀ offset, offset < 8 * count.val →
      (heap (base + BitVec.ofNat 64 offset)).isSome = true ∧ permit (base + BitVec.ofNat 64 offset) = true),
      ∃ updated : AddressHeap,
      exec (liftPermission permit) storeProgram (storeInput (liftHeap heap) ⟨base.toNat, count⟩ value) =
        some (.unit, liftHeap updated) ∧
      (∀ lane byte : Fin 8, lane.val < count.val →
        updated (base + BitVec.ofNat 64 (offsetOf lane byte).val) =
          some (wordByte (flatten value lane) byte)) ∧
      (∀ address, address.toNat < base.toNat ∨ base.toNat + 8 * count.val ≤ address.toNat →
        updated address = heap address)

/-- The entire unchanged original chunked XOR LLBC has finite-address semantics
under its equal-length, separated Rust-view and no-wrap premises. -/
def LlbcFiniteXorContract : Prop :=
  ∀ (heap : AddressHeap) (left right : Address) (count : Usize)
    (permit : Address → Bool) (leftWords rightWords : Nat → BitVec 64)
    (_leftFits : left.toNat + 8 * count.val ≤ 2 ^ 64)
    (_rightFits : right.toNat + 8 * count.val ≤ 2 ^ 64)
    (_leftBytes : FiniteWordWindow heap left count.val leftWords)
    (_rightBytes : FiniteWordWindow heap right count.val rightWords)
    (_writable : ∀ offset, offset < 8 * count.val →
      (heap (left + BitVec.ofNat 64 offset)).isSome = true ∧ permit (left + BitVec.ofNat 64 offset) = true)
    (_separated : AvxXorLlbc.Separated ⟨left.toNat, count⟩ ⟨right.toNat, count⟩),
      ∃ updated : AddressHeap,
      AvxXorLlbc.run AvxXorLlbc.program (liftPermission permit)
        ⟨left.toNat, count⟩ ⟨right.toNat, count⟩ (liftHeap heap) = some (liftHeap updated) ∧
      FiniteWordWindow updated left count.val (fun i => leftWords i ^^^ rightWords i) ∧
      ∀ address, address.toNat < left.toNat ∨ left.toNat + 8 * count.val ≤ address.toNat →
        updated address = heap address

/-- The original difference loop returns exactly the finite-address XOR row,
its nonzero flag, and a complete frame outside the destination. -/
def LlbcFiniteDifferenceContract : Prop :=
  ∀ (inputs : Difference.Inputs) (heap : AddressHeap)
    (permit : Address → Bool) (_admitted : Difference.Admitted inputs (liftPermission permit) (liftHeap heap))
    (_dstFits : inputs.dst.base + 8 * inputs.dst.len.val ≤ 2 ^ 64)
    (_localFits : inputs.localWords.base + 8 * inputs.localWords.len.val ≤ 2 ^ 64)
    (_remoteFits : inputs.remoteBytes.base + inputs.remoteBytes.len.val ≤ 2 ^ 64),
      ∃ (nonzero : Bool) (updated : AddressHeap),
      Difference.differenceProgram inputs (liftPermission permit) (liftHeap heap) = some (nonzero, liftHeap updated) ∧
      FiniteWordWindow updated (BitVec.ofNat 64 inputs.dst.base) inputs.dst.len.val (finiteDeltaWord inputs heap) ∧
      (nonzero = true ↔ ∃ index, index < inputs.dst.len.val ∧ finiteDeltaWord inputs heap index ≠ 0) ∧
      ∀ address, address.toNat < inputs.dst.base ∨ inputs.dst.base + 8 * inputs.dst.len.val ≤ address.toNat →
        updated address = heap address

end BulksketchBridge.X86MaskedMemory
