import Arithmetic.AvxHorizontalXorGenerated
import Arithmetic.AvxHornerChunkRuntime
import Arithmetic.MutableZipRuntime
import BulksketchBridge.AvxTileDoubleZip

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.AvxTileRuntime

open Avx512Register
open BulksketchBridge.AvxTileDoubleZip

abbrev Init := core.iter.adapters.zip.Zip (Paired Word512 Word512) (Aeneas.Std.AvxHornerChunkRuntime.ChunkState U64)
abbrev Item := (Word512 × Word512) × Slice U64
abbrev PowerIter := core.slice.iter.IterMut Word512
abbrev SharedPowerIter := core.slice.iter.Iter Word512
abbrev SharedWords := core.iter.traits.iterator.Iterator SharedPowerIter Word512
abbrev SharedArrayWords (W : Usize) :=
  core.iter.traits.collect.IntoIterator (Array Word512 W) Word512 SharedPowerIter

structure MutableWords where
structure BothMutableWords where
structure ChunkWords where
structure MutableArrayWords (W : Usize) where

def mutableWords (_ : Type) : MutableWords := ⟨⟩
def bothMutableWords (_ _ : MutableWords) : BothMutableWords := ⟨⟩
def chunkWords (_ : Type) : ChunkWords := ⟨⟩
def mutableArrayWords (_ : Type) (W : Usize) : MutableArrayWords W := ⟨⟩

class ZipConstructor (Left Right : Type) where
  Output : Type
  build : Left → Right → Output

def zipConstruct {Left Right : Type} [constructor : ZipConstructor Left Right]
    (left : Left) (right : Right) : constructor.Output :=
  constructor.build left right

def constructPair {W : Usize} (left : PowerIter) (right : Array Word512 W) :
    Result (Paired Word512 Word512 × (Paired Word512 Word512 → PowerIter) ×
      (Paired Word512 Word512 → Array Word512 W)) := do
  let (words, rebuild) ← lift (Array.to_slice_mut right)
  let (rightIter, restore) ← core.slice.Slice.iter_mut words
  .ok (⟨left, rightIter⟩, fun later => later.fst, fun later => rebuild (restore later.snd))

instance {W : Usize} : ZipConstructor MutableWords (MutableArrayWords W) where
  Output := PowerIter → Array Word512 W →
    Result (Paired Word512 Word512 × (Paired Word512 Word512 → PowerIter) ×
      (Paired Word512 Word512 → Array Word512 W))
  build _ _ := constructPair

def constructInit (left : Paired Word512 Word512) (right : Aeneas.Std.AvxHornerChunkRuntime.ChunkState U64) :
    Result (Init × (Init → Paired Word512 Word512) × (Init → Paired Word512 Word512)) :=
  .ok (⟨left, right⟩, fun later => later.fst, fun later => later.fst)

instance : ZipConstructor BothMutableWords ChunkWords where
  Output := Paired Word512 Word512 → Aeneas.Std.AvxHornerChunkRuntime.ChunkState U64 →
    Result (Init × (Init → Paired Word512 Word512) × (Init → Paired Word512 Word512))
  build _ _ := constructInit

instance {W : Usize} : ZipConstructor MutableWords (SharedArrayWords W) where
  Output := PowerIter → Array Word512 W →
    Result (MutableZip.State Word512 Word512 × (MutableZip.State Word512 Word512 → PowerIter))
  build _ right := MutableZip.construct right

class ZipNext (Left Right : Type) where
  Output : Type
  next : Left → Right → Output

def zipNext {Left Right : Type} [iterator : ZipNext Left Right]
    (left : Left) (right : Right) : iterator.Output :=
  iterator.next left right

def nextInit (state : Init) :
    Result (Option Item × Init × (Init → Option Item → Init) × (Init → Option Item → Init)) :=
  if state.fst.fst.i < state.fst.fst.slice.length ∧ state.fst.snd.i < state.fst.snd.slice.length ∧
      state.snd.offset < state.snd.words.length then do
    let (pair, nextPair, _) ← nextBoth state.fst
    let (words, nextChunk) ← Aeneas.Std.AvxHornerChunkRuntime.nextShared state.snd
    .ok (pair.bind fun items => words.map fun chunk => (items, chunk), ⟨nextPair, nextChunk⟩,
      fun later replacement => ⟨⟨overwrite state.fst.fst.i later.fst.fst
        (replacement.map fun item => item.fst.fst), later.fst.snd⟩, later.snd⟩,
      fun later replacement => ⟨⟨later.fst.fst, overwrite state.fst.snd.i later.fst.snd
        (replacement.map fun item => item.fst.snd)⟩, later.snd⟩)
  else .ok (none, state, fun later _ => later, fun later _ => later)

instance : ZipNext BothMutableWords ChunkWords where
  Output := Init →
    Result (Option Item × Init × (Init → Option Item → Init) × (Init → Option Item → Init))
  next _ _ := nextInit

instance : ZipNext MutableWords SharedWords where
  Output := MutableZip.State Word512 Word512 →
    Result (Option (Word512 × Word512) × MutableZip.State Word512 Word512 ×
      (MutableZip.State Word512 Word512 → Option (Word512 × Word512) → MutableZip.State Word512 Word512))
  next _ right := MutableZip.next core.slice.iter.IteratorIterMut.next right

def vectorCopy : core.marker.Copy Word512 := { cloneInst := { clone := fun value => .ok value } }

def copied (_ : SharedWords) (_ : core.marker.Copy Word512) (_ : SharedWords)
    (iterator : SharedPowerIter) : Result SharedPowerIter :=
  .ok iterator

def foldCopied {F : Type} (_ : SharedWords) (_ : core.marker.Copy Word512)
    (call : core.ops.function.FnMut F (Word512 × Word512) Word512)
    (iterator : SharedPowerIter) (initial : Word512) (closure : F) : Result Word512 := do
  let (value, _) ← (iterator.slice.val.drop iterator.i).foldlM
    (fun (value, closure) item => call.call_mut closure (value, item)) (initial, closure)
  .ok value

end Aeneas.Std.AvxTileRuntime
