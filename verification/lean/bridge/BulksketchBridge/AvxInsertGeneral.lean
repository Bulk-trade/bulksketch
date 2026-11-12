import BulksketchBridge.AvxInsertDispatch

namespace BulksketchBridge.AvxInsertGeneral

open Aeneas Aeneas.Std ControlFlow
open Aeneas.Std.AvxHornerChunkRuntime Aeneas.Std.AvxInsertDispatchRuntime
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private def chunksAt (ids : Slice U64) (offset : Nat) : ChunkState U64 :=
  ⟨ids, offset, 32⟩

def selectTile (tile : Tile) (odd ids : Slice U64) : Result (Slice U64) :=
  if ids.length ≤ 8 then tile 1#usize true odd ids
  else if ids.length ≤ 16 then tile 2#usize true odd ids
  else tile 4#usize false odd ids

def foldTiles (tile : Tile) (ids : Slice U64) (offset : Nat) (odd : Slice U64) :
    Result (Slice U64) :=
  if _active : offset < ids.length then do
    let stop := min (offset + 32) ids.length
    let odd' ← selectTile tile odd (window ids offset stop)
    foldTiles tile ids stop odd'
  else .ok odd
termination_by ids.length - offset
decreasing_by omega

theorem tile_step (tile : Tile) (odd ids : Slice U64) (offset : Nat)
    (active : offset < ids.length) :
    let stop := min (offset + 32) ids.length
    insert_loop3.body tile (chunksAt ids offset) odd = (do
      let odd' ← selectTile tile odd (window ids offset stop)
      .ok (.cont (chunksAt ids stop, odd'))) := by
  dsimp only
  let stop := min (offset + 32) ids.length
  let part := window ids offset stop
  have next : nextShared (chunksAt ids offset) =
      .ok (some part, chunksAt ids stop) := by simp [nextShared, chunksAt, active, part, stop]
  have positive : 0 < part.length := by
    simp only [part, window, Slice.length, Slice.from_val, List.slice_length]
    change 0 < min (ids.length - offset) (stop - offset)
    dsimp only [stop]
    omega
  have lo : 1#usize ≤ part.len := by
    change (1#usize).val ≤ part.len.val
    rw [Slice.len_val]
    change 1 ≤ part.length
    omega
  have low : (part.len ≤ 8#usize) = (part.length ≤ 8) := by
    change (part.len.val ≤ (8#usize).val) = _
    rw [Slice.len_val]
    rfl
  have mid : (9#usize ≤ part.len) = (9 ≤ part.length) := by
    change ((9#usize).val ≤ part.len.val) = _
    rw [Slice.len_val]
    rfl
  have high : (part.len ≤ 16#usize) = (part.length ≤ 16) := by
    change (part.len.val ≤ (16#usize).val) = _
    rw [Slice.len_val]
    rfl
  change _ = (do let odd' ← selectTile tile odd part; .ok (ControlFlow.cont (chunksAt ids stop, odd')))
  simp only [insert_loop3.body, next, bind_ok]
  dsimp! only
  simp only [lo, low, mid, high, ite_true, Slice.len_val, selectTile]
  cases h : part.length with
  | zero => omega
  | succ n =>
    by_cases h8 : n < 8
    · simp [h8]; rfl
    · have h9 : 8 ≤ n := by omega
      by_cases h16 : n < 16 <;> simp [h8, h9, h16] <;> rfl

theorem fold_refines (tile : Tile) (ids : Slice U64) (offset : Nat) (odd : Slice U64) :
    insert_loop3 tile (chunksAt ids offset) odd = foldTiles tile ids offset odd := by
  rw [foldTiles, insert_loop3, loop]
  dsimp only
  by_cases active : offset < ids.length
  · rw [dite_eq_left active, tile_step tile odd ids offset active]
    simp only [Aeneas.Std.bind_assoc, bind_ok]
    congr 1
    funext next
    exact fold_refines tile ids (min (offset + 32) ids.length) next
  · rw [dite_eq_right active]
    have stop : nextShared (chunksAt ids offset) = .ok (none, chunksAt ids offset) := by
      simp [nextShared, chunksAt, active]
    have doneBody : insert_loop3.body tile (chunksAt ids offset) odd = .ok (.done odd) := by
      simp only [insert_loop3.body, stop, bind_ok]
      rfl
    simp only [doneBody, bind_ok]
termination_by ids.length - offset
decreasing_by omega

private theorem start_chunks (ids : Slice U64) :
    chunks ids 32#usize = .ok (chunksAt ids 0) := by simp [chunks, chunksAt]

private theorem first_word (ids : Slice U64) (positive : 0 < ids.length) :
    Slice.index_usize ids 0#usize = .ok ids[0]! := by
  obtain ⟨value, normal, read⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec ids 0#usize (by exact positive))
  rw [normal, read, Slice.getElem!_Nat_eq]
  with_unfolding_all exact (congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ positive))

def batchDispatch (sparse : Batch) (tile : Tile) (odd ids : Slice U64) : Result (Slice U64) :=
  if ids.length ≤ 4 then
    match odd.length with
    | 18 | 72 | 89 => sparse odd ids
    | _ => foldTiles tile ids 0 odd
  else foldTiles tile ids 0 odd

def freeDispatch (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch)
    (tile : Tile) (odd ids : Slice U64) : Result (Slice U64) :=
  if odd.length = 0 ∨ ids.length = 0 then .ok odd
  else if ids.length = 1 then
    match odd.length with
    | 18 => one18 odd ids[0]!
    | 32 => one32 odd ids[0]!
    | 72 => single 72#usize odd ids[0]!
    | 89 => single 89#usize odd ids[0]!
    | _ => batchDispatch sparse tile odd ids
  else batchDispatch sparse tile odd ids

/-- All original free dispatch branches refine the chunk and leaf-call spec.
The named leaf implementations remain parameters, including error behavior. -/
def ActualFreeInsert : Prop :=
  ∀ (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch) (tile : Tile) (odd ids : Slice U64),
    bulksketch.backend.x86_vpclmul512.insert one18 one32 single sparse tile odd ids =
      freeDispatch one18 one32 single sparse tile odd ids

theorem free_refines : ActualFreeInsert := by
  intro one18 one32 single sparse tile odd ids
  have one : (ids.len = 1#usize) = (ids.length = 1) := by
    apply propext
    constructor
    · intro eq
      have value := congrArg UScalar.val eq
      rw [Slice.len_val] at value
      exact value
    · intro eq
      apply UScalar.eq_of_val_eq
      rw [Slice.len_val]
      exact eq
  have small : (ids.len ≤ 4#usize) = (ids.length ≤ 4) := by
    change (ids.len.val ≤ (4#usize).val) = _
    rw [Slice.len_val]
    rfl
  have loop0 : insert_loop0 tile (chunksAt ids 0) odd = foldTiles tile ids 0 odd :=
    fold_refines tile ids 0 odd
  have loop1 : insert_loop1 tile (chunksAt ids 0) odd = foldTiles tile ids 0 odd :=
    fold_refines tile ids 0 odd
  have loop2 : insert_loop2 tile (chunksAt ids 0) odd = foldTiles tile ids 0 odd :=
    fold_refines tile ids 0 odd
  have loop3 := fold_refines tile ids 0 odd
  simp only [bulksketch.backend.x86_vpclmul512.insert, freeDispatch, batchDispatch,
    core.slice.Slice.is_empty, bind_ok, one, small, Slice.len_val, start_chunks ids]
  by_cases emptyOdd : odd.length = 0
  · simp [emptyOdd]
  · by_cases emptyIds : ids.length = 0
    · simp [emptyOdd, emptyIds]
    · have read := first_word ids (by omega)
      simp only [emptyOdd, emptyIds, decide_false, Bool.false_eq_true, ite_false,
        or_self, read, bind_ok]
      by_cases onlyOne : ids.length = 1
      · simp only [onlyOne, ite_true, loop0, loop1]
        rfl
      · simp only [onlyOne, ite_false, loop2, loop3]
        rfl

end BulksketchBridge.AvxInsertGeneral
