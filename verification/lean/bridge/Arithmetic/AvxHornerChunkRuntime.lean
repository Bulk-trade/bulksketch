import Arithmetic.AvxSquareRuntime
import Arithmetic.X86PclmulHornerGenerated

namespace Aeneas.Std.AvxHornerChunkRuntime

/-- Virtual slice cursor for the pinned forward TrustedRandomAccess Zip of
Chunks and ChunksMut. The pair index in Rust corresponds to these offsets. -/
structure ChunkState (T : Type) where
  words : Slice T
  offset : Nat
  width : Nat

abbrev ZipState (T U : Type) := core.iter.adapters.zip.Zip (ChunkState T) (ChunkState U)
abbrev SharedNext (T : Type) := ChunkState T → Result (Option (Slice T) × ChunkState T)
abbrev MutableNext (T : Type) :=
  ChunkState T → Result (Option (Slice T) × ChunkState T ×
    (ChunkState T → Option (Slice T) → ChunkState T))

def window {T : Type} (words : Slice T) (start stop : Nat) : Slice T :=
  Slice.from (words.val.slice start stop)
    ((List.slice_length_le start stop words.val).trans words.length_ineq)

def chunks {T : Type} (words : Slice T) (width : Usize) : Result (ChunkState T) :=
  if width.val = 0 then .fail .panic else .ok ⟨words, 0, width.val⟩

def chunksMut {T : Type} (words : Slice T) (width : Usize) :
    Result (ChunkState T × (ChunkState T → Slice T)) := do
  let state ← chunks words width
  .ok (state, fun later => later.words)

def nextShared {T : Type} : SharedNext T := fun state =>
  if state.offset < state.words.length then
    let stop := min (state.offset + state.width) state.words.length
    .ok (some (window state.words state.offset stop), { state with offset := stop })
  else .ok (none, state)

def nextMutable {T : Type} : MutableNext T := fun state => do
  let (item, advanced) ← nextShared state
  .ok (item, advanced, fun later replacement =>
    match item, replacement with
    | some _, some written => { later with words := later.words.setSlice! state.offset written.val }
    | _, _ => later)

def chunkBlanket {T : Type} (next : MutableNext T) : MutableNext T := next

def zipConstruct {T U : Type} (_ : SharedNext T) (_ : MutableNext U)
    (left : ChunkState T) (right : ChunkState U) :
    Result (ZipState T U × (ZipState T U → ChunkState U)) :=
  .ok (⟨left, right⟩, fun later => later.snd)

/-- Both Rust chunk types are TrustedRandomAccess. The specialized Zip
stops at the shorter input and leaves its pair index fixed on exhaustion.
Only the mutable right slice can be written through its saved chunk offset. -/
def zipNext {T U : Type} (left : SharedNext T) (right : MutableNext U)
    (state : ZipState T U) :
    Result (Option (Slice T × Slice U) × ZipState T U ×
      (ZipState T U → Option (Slice T × Slice U) → ZipState T U)) :=
  if state.fst.offset < state.fst.words.length ∧ state.snd.offset < state.snd.words.length then do
    let (first, nextLeft) ← left state.fst
    let (second, nextRight, restore) ← right state.snd
    .ok (first.bind fun a => second.map (fun b => (a, b)), ⟨nextLeft, nextRight⟩,
      fun later replacement => ⟨later.fst, restore later.snd (replacement.map Prod.snd)⟩)
  else .ok (none, state, fun later _ => later)

end Aeneas.Std.AvxHornerChunkRuntime
