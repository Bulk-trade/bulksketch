import BulksketchBridge.X86MaskedMemoryWindow

namespace BulksketchBridge.AvxXorLlbc

open Aeneas.Std Aeneas.Std.Avx512Register
open X86MaskedMemory

inductive ChunkOp where
  | loadLeft
  | loadRight
  | xor
  | store

structure Program where
  leftWidth : Nat
  rightWidth : Nat
  ops : List ChunkOp

/-- A chunk view is the next nonempty prefix, or an empty view at exhaustion. -/
def take (view : Llbc.SliceView) (width : Nat) : Llbc.SliceView :=
  ⟨view.base, Usize.ofNatCore (min width view.len.val) (by
    have := view.len.hBounds
    omega)⟩

def drop (view : Llbc.SliceView) (width : Nat) : Llbc.SliceView :=
  ⟨view.base + 8 * min width view.len.val, Usize.ofNatCore (view.len.val - width) (by
    have := view.len.hBounds
    omega)⟩

@[simp] theorem take_base (view : Llbc.SliceView) (width : Nat) :
    (take view width).base = view.base := rfl

@[simp] theorem take_len (view : Llbc.SliceView) (width : Nat) :
    (take view width).len.val = min width view.len.val := by simp [take]

@[simp] theorem drop_base (view : Llbc.SliceView) (width : Nat) :
    (drop view width).base = view.base + 8 * min width view.len.val := rfl

@[simp] theorem drop_len (view : Llbc.SliceView) (width : Nat) :
    (drop view width).len.val = view.len.val - width := by simp [drop]

/-- Interpret the verified SSA call sequence. Local register values are
stacked in definition order. A store consumes the top register. -/
def runChunk (permit : Nat → Bool) (left right : Llbc.SliceView) :
    List ChunkOp → List Word512 → Memory → Option Memory
  | [], [], heap => some heap
  | [], _ :: _, _ => none
  | op :: ops, values, heap => do
    match op with
    | .loadLeft =>
      let (.register value, heap) ← Llbc.exec permit Llbc.loadProgram (Llbc.loadInput heap left) | none
      runChunk permit left right ops (value :: values) heap
    | .loadRight =>
      let (.register value, heap) ← Llbc.exec permit Llbc.loadProgram (Llbc.loadInput heap right) | none
      runChunk permit left right ops (value :: values) heap
    | .xor =>
      let second :: first :: rest := values | none
      let .ok value := (xorWords first second).match | none
      runChunk permit left right ops (value :: rest) heap
    | .store =>
      let value :: rest := values | none
      let (.unit, heap) ← Llbc.exec permit Llbc.storeProgram (Llbc.storeInput heap left value) | none
      runChunk permit left right ops rest heap

/-- `ChunksMut` and `Chunks` are forward cursors over the two borrowed
views. Zip's returned pair is absent as soon as either cursor is exhausted.
Cursor cleanup and Rust's Unit return cannot change the modeled heap. -/
def run (program : Program) (permit : Nat → Bool) (left right : Llbc.SliceView)
    (heap : Memory) : Option Memory :=
  if _active : 0 < left.len.val ∧ 0 < right.len.val ∧
      0 < program.leftWidth ∧ 0 < program.rightWidth then do
    let updated ← runChunk permit (take left program.leftWidth) (take right program.rightWidth)
      program.ops [] heap
    run program permit (drop left program.leftWidth) (drop right program.rightWidth) updated
  else some heap
termination_by left.len.val
decreasing_by
  simp only [drop_len]
  omega

end BulksketchBridge.AvxXorLlbc
