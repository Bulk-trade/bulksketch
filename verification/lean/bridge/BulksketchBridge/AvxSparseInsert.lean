import Arithmetic.AvxSparseInsertGenerated
import BulksketchBridge.AvxTileChunkSum

namespace BulksketchBridge.AvxSparseInsert

open Aeneas Aeneas.Std Result Algebra.Gf64 AvxTileChunkSum
open Aeneas.Std.AvxInsertDispatchRuntime
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

def singletonId (id : U64) : Slice U64 :=
  Array.to_slice (Array.make 1#usize [id])

def sparseFold (insertModel : Batch) : List U64 → Slice U64 → Result (Slice U64)
  | [], odd => .ok odd
  | id :: rest, odd => do
    let updated ← insertModel odd (singletonId id)
    sparseFold insertModel rest updated

def cursor (ids : Slice U64) (index : Nat) : core.slice.iter.Iter U64 := ⟨ids, index⟩

private theorem next_word (ids : Slice U64) (index : Nat) (active : index < ids.length) :
    core.slice.iter.IteratorSliceIter.next (cursor ids index) =
      .ok (some ids[index]!, cursor ids (index + 1)) := by
  have step : index < (Slice.len ids).val := by rwa [Slice.len_val]
  unfold cursor core.slice.iter.IteratorSliceIter.next
  dsimp only
  rw [dite_eq_left step]
  exact congrArg (fun value => Result.ok (some value, cursor ids (index + 1)))
    (Slice.Inhabited_getElem_eq_getElem! ids index active)

private theorem next_done (ids : Slice U64) (index : Nat) (stop : ids.length ≤ index) :
    core.slice.iter.IteratorSliceIter.next (cursor ids index) = .ok (none, cursor ids index) := by
  have inactive : ¬index < (Slice.len ids).val := by rw [Slice.len_val]; omega
  unfold cursor core.slice.iter.IteratorSliceIter.next
  dsimp only
  rw [dite_eq_right inactive]

theorem sparse_loop_refines (insertModel : Batch) (ids : Slice U64) (index : Nat) (odd : Slice U64) :
    insert_sparse_loop insertModel (cursor ids index) odd = sparseFold insertModel (ids.val.drop index) odd := by
  suffices ∀ fuel index (odd : Slice U64), ids.length - index = fuel →
      insert_sparse_loop insertModel (cursor ids index) odd = sparseFold insertModel (ids.val.drop index) odd by
    exact this _ index odd rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro index odd measure
    by_cases active : index < ids.length
    · have drop : ids.val.drop index = ids[index]! :: ids.val.drop (index + 1) := by
        rw [List.drop_eq_getElem_cons (show index < ids.val.length from active)]
        exact congrArg (fun word => word :: ids.val.drop (index + 1))
          (Slice.Inhabited_getElem_eq_getElem! ids index active)
      rw [insert_sparse_loop, loop]
      dsimp only
      rw [insert_sparse_loop.body, next_word ids index active, bind_ok]
      dsimp! only
      simp only [lift, bind_ok, Aeneas.Std.bind_assoc, drop, sparseFold]
      congr 1
      funext next
      exact ih (ids.length - (index + 1)) (by omega) (index + 1) next rfl
    · have drop : ids.val.drop index = [] := List.drop_eq_nil_of_le (by change ids.length ≤ index; omega)
      rw [insert_sparse_loop, loop]
      dsimp only
      rw [insert_sparse_loop.body, next_done ids index (by omega), bind_ok]
      dsimp! only
      rw [bind_ok, drop, sparseFold]

/-- The original sparse insertion re-enters the exact singleton dispatch
once per ID in source order. The callback's Rust result is threaded. -/
def ActualNativeSparseInsert : Prop :=
  ∀ (insertModel : Batch) (odd ids : Slice U64),
    insert_sparse insertModel odd ids = sparseFold insertModel ids.val odd

theorem native_sparse_insert : ActualNativeSparseInsert := by
  intro insertModel odd ids
  simp only [insert_sparse, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
  exact sparse_loop_refines insertModel ids 0 odd

/-- A checked singleton callback gives the odd-power update over the
complete sparse list, preserving the caller's output width. -/
theorem sparse_field_sum (insertModel : Batch) (width : Nat)
    (singletonLaw : ∀ (odd : Slice U64) (id : U64), odd.length = width →
      ∃ updated, insertModel odd (singletonId id) = .ok updated ∧ updated.length = width ∧
        ∀ row < width, toField updated[row]!.bv = toField odd[row]!.bv + oddPower row id)
    (odd : Slice U64) (ids : List U64) (shape : odd.length = width) :
    ∃ updated, sparseFold insertModel ids odd = .ok updated ∧ updated.length = width ∧
      ∀ row < width, toField updated[row]!.bv = toField odd[row]!.bv + (ids.map (oddPower row)).sum := by
  induction ids generalizing odd with
  | nil =>
    exact ⟨odd, rfl, shape, by simp⟩
  | cons id rest ih =>
    obtain ⟨first, firstRun, firstLen, firstWords⟩ := singletonLaw odd id shape
    obtain ⟨updated, restRun, length, laterWords⟩ := ih first firstLen
    refine ⟨updated, ?_, length, ?_⟩
    · rw [sparseFold, firstRun, bind_ok]
      exact restRun
    · intro row active
      rw [laterWords row active, firstWords row active]
      simp only [List.map_cons, List.sum_cons, add_assoc]

#print axioms native_sparse_insert
#print axioms sparse_field_sum

end BulksketchBridge.AvxSparseInsert
