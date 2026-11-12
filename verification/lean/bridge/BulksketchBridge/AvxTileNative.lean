import BulksketchBridge.AvxTileInitLoop
import BulksketchBridge.AvxTileSyndromeLoop

namespace BulksketchBridge.AvxTileNative

open Aeneas Aeneas.Std Result
open Aeneas.Std.Avx512Register Aeneas.Std.AvxTileRuntime
open BulksketchBridge.AvxTileInit BulksketchBridge.AvxTileSyndromeLoop
open BulksketchBridge.AvxTileDoubleZip BulksketchBridge.AvxTileSyndrome
open bulksketch.backend.x86_vpclmul512

set_option maxHeartbeats 2600000

def zero : Word512 := fun _ _ => 0

def initState (W : Usize) (ids : Slice U64) : Init :=
  let arrays := (Array.repeat W zero).to_slice
  ⟨⟨⟨arrays, 0⟩, ⟨arrays, 0⟩⟩, ⟨ids, 0, 8⟩⟩

noncomputable def arraysAfterInit (W : Usize) (ids : Slice U64) :
    Array Word512 W × Array Word512 W :=
  let initial := initState W ids
  let (steps, powers) := initWrites (remaining initial) initial
  let original := Array.repeat W zero
  (original.from_slice powers.fst.fst.slice, original.from_slice steps.fst.snd.slice)

private theorem copied_fold (W : Usize) (CL : Bool) (words : List Word512)
    (initial : Word512) (f : bulksketch.backend.x86_vpclmul512.insert_tile.closure W CL) :
    words.foldlM (fun (acc, closure) value =>
      (bulksketch.backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i W CL).call_mut
        closure (acc, value)) (m := Result) (initial, f) =
      .ok (words.foldl xorRegister initial, f) := by
  induction words generalizing initial with
  | nil => rfl
  | cons word words ih =>
    rw [List.foldlM_cons, List.foldl_cons]
    change (do
      let pair ← bulksketch.backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i.call_mut
        f (initial, word)
      words.foldlM _ pair) = _
    rw [show bulksketch.backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i.call_mut
      f (initial, word) = .ok (xorRegister initial word, f) by
        simp only [bulksketch.backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i.call_mut,
          xorWords, bind_ok]
        rfl]
    simp only [Bind.bind, bind_ok]
    exact ih (xorRegister initial word)

def indexTail (odd : Slice U64) :
    Result (Slice U64 × (Slice U64 → Slice U64)) :=
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice U64) odd { start := 1#usize }

noncomputable def expected (W : Usize) (odd ids : Slice U64) : Result (Slice U64) := do
  let (powers, steps) := arraysAfterInit W ids
  let first := powers.val.foldl xorRegister zero
  let word ← Slice.index_usize odd 0#usize
  let odd1 ← Slice.update odd 0#usize (word ^^^ ⟨AvxHorizontalXor.parity first⟩)
  let (tail, restoreTail) ← indexTail odd1
  let (output, restore) := rowWrites zero steps tail.length ⟨tail, 0⟩ id powers
  .ok (restoreTail (restore output).slice)

/-- The checked original tile has the exact two independent initialization
writebacks, first-row horizontal fold, and later odd-word callbacks. Its
result includes the source out-of-bounds case for an empty odd slice. -/
def ActualNativeTile : Prop :=
  ∀ (load : AvxSquareRuntime.Load), AvxSquare.LoadLaw load →
    ∀ W CL odd ids, insert_tile load W CL odd ids = expected W odd ids

theorem native_tile_refines : ActualNativeTile := by
  intro load law W CL odd ids
  let initial := initState W ids
  let original := Array.repeat W zero
  have pairConstruct : AvxTileRuntime.zipConstruct (mutableWords Word512)
    (mutableArrayWords Word512 W) (⟨original.to_slice, 0⟩ : PowerIter) original =
      .ok (initial.fst, fun later => later.fst, fun later => original.from_slice later.snd.slice) := by
    change constructPair (⟨original.to_slice, 0⟩ : PowerIter) original = _
    simp only [constructPair, Array.to_slice_mut, core.slice.Slice.iter_mut, lift, bind_ok]
    rfl
  have chunksConstruct : AvxHornerChunkRuntime.chunks ids 8#usize = .ok initial.snd := rfl
  have initConstruct : AvxTileRuntime.zipConstruct (bothMutableWords (mutableWords Word512)
    (mutableWords Word512)) (chunkWords U64) initial.fst initial.snd =
      .ok (initial, fun later => later.fst, fun later => later.fst) := rfl
  have initLoop := init_loop_refines load law CL initial id id (by change 8 ≤ 8; omega)
  unfold insert_tile
  simp only [AvxSquareRuntime.zero, bind_ok, Array.to_slice_mut, core.slice.Slice.iter_mut, lift]
  try dsimp! only
  change AvxTileRuntime.zipConstruct (mutableWords Word512)
    (mutableArrayWords Word512 W)
    (⟨(Array.repeat W (fun (_ : Fin 4) (_ : Bool) => (0 : BitVec 64))).to_slice, 0⟩ : PowerIter)
    (Array.repeat W (fun (_ : Fin 4) (_ : Bool) => (0 : BitVec 64))) = _ at pairConstruct
  rw [pairConstruct, bind_ok]
  try dsimp! only
  rw [chunksConstruct, bind_ok]
  rw [initConstruct, bind_ok]
  try dsimp! only
  change _ = _
  change insert_tile_loop0 load CL initial (fun s => s) (fun s => s) = _ at initLoop
  rw [initLoop, bind_ok]
  try dsimp! only
  generalize exactInit : initWrites (remaining initial) initial = initResult
  rcases initResult with ⟨stepsState, powersState⟩
  let powers := original.from_slice powersState.fst.fst.slice
  let steps := original.from_slice stepsState.fst.snd.slice
  have arraysExact : arraysAfterInit W ids = (powers, steps) := by
    unfold arraysAfterInit
    change (let (stepsState, powersState) := initWrites (remaining initial) initial
            (original.from_slice powersState.fst.fst.slice, original.from_slice stepsState.fst.snd.slice)) = _
    rw [exactInit]
  unfold expected
  rw [arraysExact]
  dsimp! only
  have foldExact :
    foldCopied (core.iter.traits.iterator.IteratorSliceIter Word512) vectorCopy
      (bulksketch.backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i W CL)
      ⟨powers.to_slice, 0⟩ zero () = .ok (powers.val.foldl xorRegister zero) := by
    simp only [foldCopied, Array.to_slice, Slice.from_val, List.drop_zero,
      copied_fold W CL powers.val zero (), bind_ok]
    rfl
  simp only [core.slice.Slice.iter, copied, bind_ok, id]
  change Aeneas.Std.bind
    (foldCopied (core.iter.traits.iterator.IteratorSliceIter Word512) vectorCopy
      (bulksketch.backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i W CL)
      ⟨powers.to_slice, 0⟩ zero ()) _ = _
  rw [foldExact, bind_ok, AvxHorizontalXor.horizontal_refines, bind_ok]
  apply congrArg (Aeneas.Std.bind (Slice.index_usize odd 0#usize))
  funext word
  apply congrArg (Aeneas.Std.bind
    (Slice.update odd 0#usize (word ^^^ ⟨AvxHorizontalXor.parity (powers.val.foldl xorRegister zero)⟩)))
  funext written
  apply congrArg (Aeneas.Std.bind (indexTail written))
  funext tailFrame
  rcases tailFrame with ⟨tail, restoreTail⟩
  change Aeneas.Std.bind
    (insert_tile_loop1 CL zero ⟨tail, 0⟩ (fun it => it) powers steps)
    (fun (out, back) => .ok (restoreTail (back out).slice)) = _
  rw [row_loop_refines, bind_ok]
  simp only [Nat.sub_zero]
  rfl

#print axioms native_tile_refines

end BulksketchBridge.AvxTileNative
