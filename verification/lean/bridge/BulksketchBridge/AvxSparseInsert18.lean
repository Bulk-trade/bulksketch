import BulksketchBridge.AvxSparseInsert
import BulksketchBridge.AvxInsertDispatch

namespace BulksketchBridge.AvxSparseInsert

open Aeneas.Std Algebra.Gf64 AvxTileChunkSum
open AvxSquareRuntime AvxInsertDispatchRuntime AvxSquare
open bulksketch.backend.x86_vpclmul512

/-- The original sparse helper at capacity 18 re-enters the original
single-ID dispatch and executes the verified native insert_18 leaf. -/
def ActualNativeSparseInsert18 : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (one32 : Single) (single : SingleCapacity) (sparse : Batch) (tile : Tile)
      (odd ids : Slice U64), odd.length = 18 →
    let one18 := insert_18 (single_bases INSERT_BASES load) load store
    ∃ updated,
      insert_sparse (insert one18 one32 single sparse tile) odd ids = .ok updated ∧
      updated.length = 18 ∧
      ∀ row < 18,
        toField updated[row]!.bv = toField odd[row]!.bv + (ids.val.map (oddPower row)).sum

theorem native_sparse_insert18 : ActualNativeSparseInsert18 := by
  intro load store loadLaw storeLaw one32 single sparse tile odd ids width one18
  let dispatch := insert one18 one32 single sparse tile
  have singleton : ∀ (frame : Slice U64) (id : U64), frame.length = 18 →
      ∃ updated, dispatch frame (singletonId id) = .ok updated ∧ updated.length = 18 ∧
        ∀ row < 18, toField updated[row]!.bv = toField frame[row]!.bv + oddPower row id := by
    intro frame id shape
    have count : (singletonId id).length = 1 := by simp [singletonId]
    have read : (singletonId id)[0]! = id := by
      simp [singletonId, Slice.getElem!_Nat_eq]
    have exactRoute := AvxInsertDispatch.free_single_18 one18 one32 single sparse tile
      frame (singletonId id) shape count
    rw [read] at exactRoute
    obtain ⟨updated, ran, length, field, _⟩ :=
      AvxInsert18.static_insert_refines load store loadLaw storeLaw frame id (by omega)
    refine ⟨updated, exactRoute.trans ran, length.trans shape, ?_⟩
    intro row active
    exact field ⟨row, active⟩
  obtain ⟨updated, folded, length, values⟩ := sparse_field_sum dispatch 18 singleton odd ids.val width
  exact ⟨updated, (native_sparse_insert dispatch odd ids).trans folded, length, values⟩

#print axioms native_sparse_insert18

end BulksketchBridge.AvxSparseInsert
