import Aeneas

namespace BulksketchBridge.X86MaskedMemory

/-- Bytes at natural addresses in an admitted, non-wrapping memory window.
`none` means a byte is unavailable. Write permission is supplied separately. -/
abbrev Memory := Nat → Option (BitVec 8)
abbrev Lanes := Fin 8 → BitVec 64

def laneOf (offset : Fin 64) : Fin 8 := ⟨offset.val / 8, by omega⟩
def byteOf (offset : Fin 64) : Fin 8 := ⟨offset.val % 8, by omega⟩
def offsetOf (lane byte : Fin 8) : Fin 64 := ⟨8 * lane.val + byte.val, by omega⟩

def enabled (mask : BitVec 8) (lane : Fin 8) : Bool := mask.getLsbD lane.val

def wordByte (word : BitVec 64) (byte : Fin 8) : BitVec 8 := word.toLEBytes[byte.val]!

def readLane (mem : Memory) (base : Nat) (lane : Fin 8) : BitVec 64 :=
  (BitVec.fromLEBytes (List.ofFn fun byte : Fin 8 =>
    (mem (base + (offsetOf lane byte).val)).getD 0)).setWidth 64

def Readable (mem : Memory) (base : Nat) (mask : BitVec 8) : Prop :=
  ∀ offset : Fin 64, enabled mask (laneOf offset) = true →
    (mem (base + offset.val)).isSome = true

def Writable (mem : Memory) (permit : Nat → Bool) (base : Nat) (mask : BitVec 8) : Prop :=
  ∀ offset : Fin 64, enabled mask (laneOf offset) = true →
    (mem (base + offset.val)).isSome = true ∧ permit (base + offset.val) = true

def readCheck (mem : Memory) (base : Nat) (mask : BitVec 8) : Bool :=
  (List.finRange 64).all fun offset =>
    if enabled mask (laneOf offset) then (mem (base + offset.val)).isSome else true

def writeCheck (mem : Memory) (permit : Nat → Bool) (base : Nat) (mask : BitVec 8) : Bool :=
  (List.finRange 64).all fun offset =>
    if enabled mask (laneOf offset) then
      (mem (base + offset.val)).isSome && permit (base + offset.val)
    else true

def writtenBytes (mem : Memory) (base : Nat) (mask : BitVec 8) (value : Lanes) : Memory :=
  fun address =>
    if within : base ≤ address ∧ address < base + 64 then
      let offset : Fin 64 := ⟨address - base, by omega⟩
      if enabled mask (laneOf offset) then some (wordByte (value (laneOf offset)) (byteOf offset))
      else mem address
    else mem address

/-- An unaligned masked load reads only enabled lanes, zeroes the others and
returns the original memory. `none` rejects an inadmissible access. -/
def load (mem : Memory) (base : Nat) (mask : BitVec 8) : Option (Lanes × Memory) :=
  if readCheck mem base mask then
    some ((fun lane => if enabled mask lane then readLane mem base lane else 0), mem)
  else none

/-- An unaligned masked store returns the new memory state explicitly.
The model rejects an inadmissible access before defining a writeback. -/
def store (mem : Memory) (permit : Nat → Bool) (base : Nat) (mask : BitVec 8)
    (value : Lanes) : Option Memory :=
  if writeCheck mem permit base mask then some (writtenBytes mem base mask value) else none

end BulksketchBridge.X86MaskedMemory
