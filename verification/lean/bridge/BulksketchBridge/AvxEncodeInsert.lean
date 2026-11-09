import BulksketchBridge.AvxSparseInsert18
import BulksketchBridge.AvxRebuiltSeed

namespace BulksketchBridge.AvxEncodeEntry

open Aeneas Aeneas.Std Algebra.Gf64
open AvxSquareRuntime AvxSquare AvxInsertDispatchRuntime AvxInsertDispatch AvxInsertGeneral
open AvxSparseInsert BulksketchBridge.AvxTileChunkSum
open bulksketch.backend.x86_vpclmul512
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (insert_nonzero)

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def Update (odd written : Slice U64) (ids : List U64) : Prop :=
  written.length = odd.length ∧
    ∀ row < odd.length, toField written[row]!.bv = toField odd[row]!.bv + (ids.map (oddPower row)).sum

def SingleLaw (call : Single) (width : Nat) : Prop :=
  ∀ (odd : Slice U64) (id : U64), odd.length = width →
    ∃ written, call odd id = .ok written ∧ Update odd written [id]

def SparseWidth (width : Nat) : Prop := width = 18 ∨ width = 72 ∨ width = 89

private theorem batch_other (sparse : Batch) (tile : Tile) (odd ids : Slice U64)
    (other : ¬ SparseWidth odd.length) :
    batchDispatch sparse tile odd ids = foldTiles tile ids 0 odd := by
  unfold batchDispatch
  split
  · split <;> first | rfl | exfalso; exact other (by unfold SparseWidth; simp_all)
  · rfl

private theorem singleton_update (load : Load) (store : Store) (loadLaw : LoadLaw load)
    (storeLaw : StoreLaw store) (one32 : Single) (one32Law : SingleLaw one32 32)
    (single : SingleCapacity) (law72 : SingleLaw (single 72#usize) 72)
    (law89 : SingleLaw (single 89#usize) 89) (sparse : Batch) (odd ids : Slice U64) (count : ids.length = 1) :
    let one18 := insert_18 (single_bases INSERT_BASES load) load store
    ∃ written, insert one18 one32 single sparse (insert_tile load) odd ids = .ok written ∧
      Update odd written ids.val := by
  intro one18
  by_cases empty : odd.length = 0
  · rw [free_refines, freeDispatch, ite_eq_left (Or.inl empty)]
    exact ⟨odd, rfl, rfl, fun row bound => (by omega : False).elim⟩
  have active : 0 < odd.length := by omega
  have list : ids.val = [ids[0]!] := by
    have length : ids.val.length = 1 := count
    obtain ⟨head, tail, contents⟩ := List.exists_cons_of_ne_nil (l := ids.val) (by
      intro nil; rw [nil] at length; contradiction)
    rw [contents, List.length_cons] at length
    have emptyTail : tail = [] := List.length_eq_zero_iff.mp (by omega)
    simp [Slice.getElem!_Nat_eq, contents, emptyTail]
  rw [free_refines, freeDispatch, ite_eq_right (by omega : ¬ (odd.length = 0 ∨ ids.length = 0)),
    ite_eq_left count]
  by_cases h18 : odd.length = 18
  · rw [h18, list]
    obtain ⟨written, normal, length, field, _⟩ :=
      AvxInsert18.static_insert_refines load store loadLaw storeLaw odd ids[0]! (by omega)
    refine ⟨written, normal, length, ?_⟩
    intro row bound
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, oddPower] using
      field ⟨row, by omega⟩
  by_cases h32 : odd.length = 32
  · rw [h32, list]
    exact one32Law odd ids[0]! h32
  by_cases h72 : odd.length = 72
  · rw [h72, list]
    exact law72 odd ids[0]! h72
  by_cases h89 : odd.length = 89
  · rw [h89, list]
    exact law89 odd ids[0]! h89
  have other : ¬ SparseWidth odd.length := by simp [SparseWidth, h18, h72, h89]
  have route : (match odd.length with
      | 18 => one18 odd ids[0]!
      | 32 => one32 odd ids[0]!
      | 72 => single 72#usize odd ids[0]!
      | 89 => single 89#usize odd ids[0]!
      | _ => batchDispatch sparse (insert_tile load) odd ids) =
      foldTiles (insert_tile load) ids 0 odd := by
    split <;> first | exact batch_other _ _ _ _ other | contradiction
  obtain ⟨written, ran, length, words⟩ := AvxRebuiltSeed.fold_tiles_odd_sums load loadLaw ids 0 odd active
  exact ⟨written, route.trans ran, length, by simpa only [List.drop_zero] using words⟩

private theorem singleton_reentry_independent (one18 one32 : Single) (single : SingleCapacity)
    (left right : Batch) (tile : Tile) (odd ids : Slice U64) (one : ids.length = 1) :
    insert one18 one32 single left tile odd ids = insert one18 one32 single right tile odd ids := by
  rw [free_refines one18 one32 single left tile odd ids,
    free_refines one18 one32 single right tile odd ids]
  unfold freeDispatch
  by_cases empty : odd.length = 0 ∨ ids.length = 0
  · simp only [empty, ite_true]
  simp only [ite_eq_right empty]
  simp only [one, ite_true]
  by_cases h18 : odd.length = 18
  · rw [h18]
    rfl
  by_cases h32 : odd.length = 32
  · rw [h32]
    rfl
  by_cases h72 : odd.length = 72
  · rw [h72]
    rfl
  by_cases h89 : odd.length = 89
  · rw [h89]
    rfl
  have other : ¬ SparseWidth odd.length := by simp [SparseWidth, h18, h72, h89]
  have same (sparse : Batch) :
      (match odd.length with
        | 18 => one18 odd ids[0]!
        | 32 => one32 odd ids[0]!
        | 72 => single 72#usize odd ids[0]!
        | 89 => single 89#usize odd ids[0]!
        | _ => batchDispatch sparse tile odd ids) = foldTiles tile ids 0 odd := by
    split <;> first | exact batch_other _ _ _ _ other | contradiction
  exact (same left).trans (same right).symm

/-- Every actual sparse reentry calls the native insertion with a one-ID
slice. The nested sparse slot has no observable effects on any input. -/
theorem sparse_reentry_independent (one18 one32 : Single) (single : SingleCapacity)
    (left right : Batch) (tile : Tile) (odd ids : Slice U64) :
    insert_sparse (insert one18 one32 single left tile) odd ids =
      insert_sparse (insert one18 one32 single right tile) odd ids := by
  rw [native_sparse_insert, native_sparse_insert]
  suffices ∀ (values : List U64) (frame : Slice U64),
      sparseFold (insert one18 one32 single left tile) values frame =
        sparseFold (insert one18 one32 single right tile) values frame from this ids.val odd
  intro values
  induction values with
  | nil => intro frame; rfl
  | cons id rest ih =>
    intro frame
    have one : (singletonId id).length = 1 := by simp [singletonId]
    simp only [sparseFold, singleton_reentry_independent one18 one32 single left right tile frame _ one]
    congr 1
    funext next
    exact ih next

/-- The original sparse loop reenters the original free dispatch. At the
three actual sparse widths its call is always a specialized singleton. -/
def nativeSparse (load : Load) (store : Store) (one32 : Single) (single : SingleCapacity) : Batch :=
  insert_sparse
    (insert (insert_18 (single_bases INSERT_BASES load) load store) one32 single
      (fun odd _ => .ok odd) (insert_tile load))

def nativeInsert (load : Load) (store : Store) (one32 : Single) (single : SingleCapacity)
    {F : Type} (field : bulksketch.field.BinaryField F) : Batch :=
  insert_nonzero (insert_18 (single_bases INSERT_BASES load) load store)
    one32 single (nativeSparse load store one32 single) (insert_tile load) field

private theorem sparse_update (load : Load) (store : Store) (loadLaw : LoadLaw load)
    (storeLaw : StoreLaw store) (one32 : Single) (one32Law : SingleLaw one32 32)
    (single : SingleCapacity) (law72 : SingleLaw (single 72#usize) 72)
    (law89 : SingleLaw (single 89#usize) 89) (odd ids : Slice U64) :
    ∃ written, nativeSparse load store one32 single odd ids = .ok written ∧ Update odd written ids.val := by
  unfold nativeSparse
  rw [native_sparse_insert]
  let call := insert (insert_18 (single_bases INSERT_BASES load) load store)
    one32 single (fun odd _ => .ok odd) (insert_tile load)
  have exactSingleton (frame : Slice U64) (id : U64) (width : frame.length = odd.length) :
      ∃ written, call frame (singletonId id) = .ok written ∧ written.length = odd.length ∧
        ∀ row < odd.length, toField written[row]!.bv = toField frame[row]!.bv + oddPower row id := by
    have one : (singletonId id).length = 1 := by simp [singletonId]
    have contents : (singletonId id).val = [id] := by simp [singletonId]
    obtain ⟨written, normal, length, words⟩ :=
      singleton_update load store loadLaw storeLaw one32 one32Law single law72 law89
        (fun odd _ => .ok odd) frame (singletonId id) one
    rw [contents] at words
    refine ⟨written, normal, length.trans width, ?_⟩
    intro row bound
    simpa using words row (by omega)
  obtain ⟨written, normal, length, words⟩ := sparse_field_sum call odd.length exactSingleton odd ids.val rfl
  exact ⟨written, normal, length, words⟩

/-- Exact native routing for every width and every input list. Its only
leaf obligations are the original 32 and const-specialized 72/89 bodies. -/
def ActualAvxInsertAllRoutes : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (one32 : Single), SingleLaw one32 32 →
    ∀ (single : SingleCapacity), SingleLaw (single 72#usize) 72 → SingleLaw (single 89#usize) 89 →
    ∀ odd ids, ∃ written, nativeInsert load store one32 single gf64 odd ids = .ok written ∧ Update odd written ids.val

theorem avx_insert_all_routes : ActualAvxInsertAllRoutes := by
  intro load store loadLaw storeLaw one32 one32Law single law72 law89 odd ids
  unfold nativeInsert
  rw [public_dispatch_refines]
  by_cases empty : odd.length = 0 ∨ ids.length = 0
  · rw [ite_eq_left empty]
    refine ⟨odd, rfl, rfl, ?_⟩
    intro row bound
    have noIds : ids.length = 0 := by omega
    rw [show ids.val = [] from List.length_eq_zero_iff.mp noIds]
    simp
  rw [ite_eq_right empty]
  by_cases one : ids.length = 1
  · exact singleton_update load store loadLaw storeLaw one32 one32Law single law72 law89 _ odd ids one
  rw [free_refines, freeDispatch, ite_eq_right empty, ite_eq_right one]
  by_cases sparseShape : ids.length ≤ 4 ∧ SparseWidth odd.length
  · obtain ⟨count, shape⟩ := sparseShape
    rcases shape with width | width | width <;>
      simp only [batchDispatch, count, ite_true, width] <;>
      exact sparse_update load store loadLaw storeLaw one32 one32Law single law72 law89 odd ids
  have route : batchDispatch (nativeSparse load store one32 single) (insert_tile load) odd ids =
      foldTiles (insert_tile load) ids 0 odd := by
    by_cases few : ids.length ≤ 4
    · exact batch_other _ _ _ _ (fun width => sparseShape ⟨few, width⟩)
    · simp only [batchDispatch, few, ite_false]
  rw [route]
  obtain ⟨written, normal, length, values⟩ :=
    AvxRebuiltSeed.fold_tiles_odd_sums load loadLaw ids 0 odd (by omega)
  exact ⟨written, normal, length, by simpa only [List.drop_zero] using values⟩

#print axioms avx_insert_all_routes

end BulksketchBridge.AvxEncodeEntry
