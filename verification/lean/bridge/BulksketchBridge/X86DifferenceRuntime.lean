import BulksketchBridge.X86MaskedMemoryWindow

namespace BulksketchBridge.X86MaskedMemory.Difference

open Aeneas.Std Aeneas.Std.Avx512Register

structure Inputs where
  dst : Llbc.SliceView
  localWords : Llbc.SliceView
  remoteBytes : Llbc.SliceView

structure Cursor where
  start : Nat
  stop : Nat
  stride : Nat

structure State where
  heap : Memory
  any : Word512

def checked (value : Nat) : Option Nat :=
  if value ≤ Usize.max then some value else none

def checkedSub (left right : Nat) : Option Nat :=
  if right ≤ left then some (left - right) else none

def wordRange (view : Llbc.SliceView) (bounds : Nat × Nat) : Option Llbc.SliceView :=
  if h : bounds.1 ≤ bounds.2 ∧ bounds.2 ≤ view.len.val then
    some ⟨view.base + 8 * bounds.1,
      Usize.ofNatCore (bounds.2 - bounds.1) (by
        have upper := view.len.hBounds
        omega)⟩
  else none

def byteAdd (pointer : Llbc.SliceView) (offset : Nat) : Option Llbc.SliceView :=
  if h : offset ≤ pointer.len.val then
    some ⟨pointer.base + offset,
      Usize.ofNatCore (pointer.len.val - offset) (by
        have upper := pointer.len.hBounds
        omega)⟩
  else none

def sourceMask (len : Nat) : Option (BitVec 8) := do
  if h : len ≤ 8 then
    let len := Usize.ofNatCore len (by scalar_tac)
    let .ok mask := (bulksketch.backend.x86_vpclmul512.mask len).match | none
    some mask.bv
  else none

def loadWords (permit : Nat → Bool) (heap : Memory) (view : Llbc.SliceView) :
    Option (Word512 × Memory) := do
  let (.register value, heap) ← Llbc.exec permit Llbc.loadProgram (Llbc.loadInput heap view) | none
  some (value, heap)

def remoteCheck (mask : BitVec 8) (bytes : Nat) : Bool :=
  (List.finRange 64).all fun offset =>
    if enabled mask (laneOf offset) then decide (offset.val < bytes) else true

/-- The source raw load uses the original mask at a byte pointer into remote.
Every enabled byte must remain within that view. -/
def loadRemote (heap : Memory) (mask : BitVec 8) (pointer : Llbc.SliceView) :
    Option (Word512 × Memory) := do
  if remoteCheck mask pointer.len.val then
    let (value, heap) ← X86MaskedMemory.load heap pointer.base mask
    some (unflatten value, heap)
  else none

def storeWords (permit : Nat → Bool) (heap : Memory) (view : Llbc.SliceView) (value : Word512) :
    Option Memory := do
  let (.unit, heap) ← Llbc.exec permit Llbc.storeProgram (Llbc.storeInput heap view value) | none
  some heap

def zeroRegister : Word512 := fun _ _ => 0

def xorValue (a b : Word512) : Word512 := fun pair high => a pair high ^^^ b pair high

def orValue (a b : Word512) : Word512 := fun pair high => a pair high ||| b pair high

/-- The self TEST instruction has a nonzero mask exactly when a lane is
nonzero. Only the nonzero predicate of its mask is consumed by Rust. -/
def testSelfNonzero (register : Word512) : Bool :=
  (List.finRange 8).any fun lane => decide (flatten register lane ≠ 0)

/-- Checked iteration of the normal StepBy range. The generated entry
supplies the original start, stop, stride and body. -/
def run (body : Nat → State → Option State) (cursor : Cursor) : Nat → State → Option State
  | 0, _ => none
  | fuel + 1, state => do
    if cursor.start < cursor.stop then
      let state ← body cursor.start state
      run body {cursor with start := min (cursor.start + cursor.stride) cursor.stop} fuel state
    else some state

end BulksketchBridge.X86MaskedMemory.Difference
