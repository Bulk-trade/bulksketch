import Arithmetic.AvxHornerChunkRuntime

namespace Aeneas.Std.AvxSliceKernelRuntime

open Aeneas Aeneas.Std Result

abbrev ChunkState := AvxHornerChunkRuntime.ChunkState
abbrev State (T U : Type) := core.iter.adapters.zip.Zip (ChunkState T) (ChunkState U)
abbrev SharedNext := AvxHornerChunkRuntime.SharedNext
abbrev MutableNext := AvxHornerChunkRuntime.MutableNext

abbrev Xor := Slice U64 → Slice U64 → Result (Slice U64)

def sharedBlanket {T : Type} (next : SharedNext T) : SharedNext T := next

def zipConstruct {T U : Type} (_ : MutableNext T) (_ : SharedNext U)
    (left : ChunkState T) (right : ChunkState U) :
    Result (State T U × (State T U → ChunkState T)) :=
  .ok (⟨left, right⟩, fun later => later.fst)

/-- The pinned Rust specialized Zip takes one chunk from each side
while both cursors have data. The mutable callback writes the saved
destination range into the later iterator state. -/
def zipNext {T U : Type} (left : MutableNext T) (right : SharedNext U)
    (state : State T U) :
    Result (Option (Slice T × Slice U) × State T U ×
      (State T U → Option (Slice T × Slice U) → State T U)) :=
  if state.fst.offset < state.fst.words.length ∧ state.snd.offset < state.snd.words.length then do
    let (first, nextLeft, restore) ← left state.fst
    let (second, nextRight) ← right state.snd
    .ok (first.bind fun a => second.map (fun b => (a, b)), ⟨nextLeft, nextRight⟩,
      fun later replacement => ⟨restore later.fst (replacement.map Prod.fst), later.snd⟩)
  else .ok (none, state, fun later _ => later)

end Aeneas.Std.AvxSliceKernelRuntime
