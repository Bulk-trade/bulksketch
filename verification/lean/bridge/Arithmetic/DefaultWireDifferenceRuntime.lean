import Arithmetic.MutableZipRuntime

namespace BulksketchBridge.DefaultWireDifferenceRuntime

open Aeneas Aeneas.Std Result

abbrev WordZip := MutableZip.State U64 U64
abbrev ByteChunks := core.slice.iter.ChunksExact U8
abbrev State := core.iter.adapters.zip.Zip WordZip ByteChunks
abbrev Item := (U64 × U64) × Slice U8
abbrev Back := State → State

/-- Both nested Rust Zip constructors move their left operand. The original
shared right operand is represented by its pinned IntoIterator result. -/
def zip {Left Right Item Input Dictionary : Type} (_ : Dictionary)
    (right : core.iter.traits.collect.IntoIterator Input Item Right)
    (left : Left) (input : Input) :
    Result (core.iter.adapters.zip.Zip Left Right ×
      (core.iter.adapters.zip.Zip Left Right → Left)) := do
  let iterator ← right.into_iter input
  ok (⟨left, iterator⟩, fun state => state.fst)

abbrev InnerDictionary :=
  MutableZip.LeftNext U64 × core.iter.traits.iterator.Iterator (core.slice.iter.Iter U64) U64

def innerDictionary (left : MutableZip.LeftNext U64)
    (right : core.iter.traits.iterator.Iterator (core.slice.iter.Iter U64) U64) :
    InnerDictionary := (left, right)

/-- The pinned Rust outer Zip uses the trusted random-access specialization.
An exhausted side leaves the virtual cursors fixed. Only the leftmost
mutable iterator has a backward update. -/
def next (left : InnerDictionary)
    (right : core.iter.traits.iterator.Iterator ByteChunks (Slice U8)) (state : State) :
    Result (Option Item × State × (State → Option Item → State)) :=
  match state.snd.chunks with
  | [] => ok (none, state, fun later _ => later)
  | _ :: _ => do
    let (pair, nextLeft, restoreLeft) ← MutableZip.next left.1 left.2 state.fst
    match pair with
    | none => ok (none, ⟨nextLeft, state.snd⟩,
        fun later _ => ⟨restoreLeft later.fst none, later.snd⟩)
    | some words => do
      let (chunk, nextRight) ← right.next state.snd
      ok (chunk.map (words, ·), ⟨nextLeft, nextRight⟩,
        fun later replacement =>
          ⟨restoreLeft later.fst (chunk.bind fun _ => replacement.map Prod.fst), later.snd⟩)

end BulksketchBridge.DefaultWireDifferenceRuntime
