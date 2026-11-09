import Arithmetic.AvxInsertDispatchGenerated
import BulksketchBridge.AvxInsert18

namespace BulksketchBridge.AvxInsertDispatch

open Aeneas Aeneas.Std ControlFlow
open Aeneas.Std.AvxHornerChunkRuntime Aeneas.Std.AvxInsertDispatchRuntime
open Aeneas.Std.AvxSquareRuntime AvxSquare
open Algebra.Gf64
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

abbrev gf64 := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

private theorem read_first (ids : Slice U64) (positive : 0 < ids.length) :
    Slice.index_usize ids 0#usize = .ok ids[0]! := by
  obtain ⟨value, normal, read⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec ids 0#usize (by exact positive))
  rw [normal, read, Slice.getElem!_Nat_eq]
  with_unfolding_all exact (congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ positive))

private theorem len_eq (words : Slice U64) (length : Usize) (same : words.length = length.val) :
    words.len = length := UScalar.eq_of_val_eq (by rwa [Slice.len_val])

theorem free_single_18 (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch) (tile : Tile)
    (odd ids : Slice U64) (capacity : odd.length = 18) (count : ids.length = 1) :
    insert one18 one32 single sparse tile odd ids = one18 odd ids[0]! := by
  have out : odd.len = 18#usize := len_eq _ _ (by simpa using capacity)
  have input : ids.len = 1#usize := len_eq _ _ (by simpa using count)
  have read := read_first ids (by omega)
  simp only [bulksketch.backend.x86_vpclmul512.insert, core.slice.Slice.is_empty,
    capacity, count, out, input, bind_ok, read]
  rfl

private def chunksAt (ids : Slice U64) (offset : Nat) : ChunkState U64 := ⟨ids, offset, 32⟩

private theorem full_chunk (ids : Slice U64) :
    window ids 0 ids.length = ids := by
  apply Slice.ext
  simp [window, List.slice]

/-- For the admitted 17–32 ID case, the native leaf callback receives the
entire ID slice exactly once, with W=4 and the shift reduction mode. -/
theorem one_full_tile (tile : Tile) (odd ids result : Slice U64)
    (large : 16 < ids.length) (room : ids.length ≤ 32)
    (called : tile 4#usize false odd ids = .ok result) :
    insert_loop3 tile (chunksAt ids 0) odd = .ok result := by
  have next : nextShared (chunksAt ids 0) =
      .ok (some ids, chunksAt ids ids.length) := by
    have nonempty : 0 < ids.length := by omega
    unfold nextShared chunksAt
    simp only [nonempty, ite_true, full_chunk ids, Nat.zero_add, Nat.min_eq_right room]
  have stop : nextShared (chunksAt ids ids.length) = .ok (none, chunksAt ids ids.length) := by
    simp only [nextShared, chunksAt, Nat.lt_irrefl, ite_false]
  have doneBody : insert_loop3.body tile (chunksAt ids ids.length) result = .ok (.done result) := by
    simp only [insert_loop3.body, stop, bind_ok]
    rfl
  have activeBody : insert_loop3.body tile (chunksAt ids 0) odd =
      .ok (.cont (chunksAt ids ids.length, result)) := by
    simp only [insert_loop3.body, next, bind_ok]
    dsimp! only
    have one : 1#usize ≤ ids.len := by change (1#usize).val ≤ ids.len.val; rw [Slice.len_val]; change 1 ≤ ids.length; omega
    have eight : ¬ ids.len ≤ 8#usize := by change ¬ids.len.val ≤ (8#usize).val; rw [Slice.len_val]; change ¬ids.length ≤ 8; omega
    have nine : 9#usize ≤ ids.len := by change (9#usize).val ≤ ids.len.val; rw [Slice.len_val]; change 9 ≤ ids.length; omega
    have sixteen : ¬ ids.len ≤ 16#usize := by change ¬ids.len.val ≤ (16#usize).val; rw [Slice.len_val]; change ¬ids.length ≤ 16; omega
    simp only [Slice.len_val]
    cases size : ids.length with
    | zero => omega
    | succ n =>
      simp only [one, eight, nine, sixteen, ite_true, ite_false, called, bind_ok]
  unfold insert_loop3 loop
  dsimp only
  rw [activeBody, bind_ok]
  dsimp only
  rw [loop, doneBody, bind_ok]

theorem free_large_single_tile (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch) (tile : Tile)
    (odd ids result : Slice U64) (out : 0 < odd.length)
    (large : 16 < ids.length) (room : ids.length ≤ 32)
    (called : tile 4#usize false odd ids = .ok result) :
    insert one18 one32 single sparse tile odd ids = .ok result := by
  have notOne : ids.len ≠ 1#usize := by
    intro same
    have value := congrArg UScalar.val same
    simp only [Slice.len_val] at value
    change ids.length = 1 at value
    omega
  have notSmall : ¬ ids.len ≤ 4#usize := by
    change ¬ ids.len.val ≤ (4#usize).val
    rw [Slice.len_val]
    change ¬ids.length ≤ 4
    omega
  have outputNonempty : ¬odd.length = 0 := by omega
  have inputNonempty : ¬ids.length = 0 := by omega
  have start : chunks ids 32#usize = .ok (chunksAt ids 0) := by simp [chunks, chunksAt]
  simp only [bulksketch.backend.x86_vpclmul512.insert, core.slice.Slice.is_empty, outputNonempty, inputNonempty, decide_false,
    Bool.false_eq_true, ite_false, bind_ok, notOne, notSmall, start]
  exact one_full_tile tile odd ids result large room called

/-- The GF64 public selector executes the original free dispatch on every
nonempty input and preserves the output for either empty input. -/
def ActualInsertDispatch : Prop :=
  ∀ (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch) (tile : Tile) (odd ids : Slice U64),
    bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
      one18 one32 single sparse tile gf64 odd ids =
      if odd.length = 0 ∨ ids.length = 0 then .ok odd else insert one18 one32 single sparse tile odd ids

theorem public_dispatch_refines : ActualInsertDispatch := by
  intro one18 one32 single sparse tile odd ids
  have bits : bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = 64#u32 := by
    simp only [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
  by_cases emptyOdd : odd.length = 0
  · simp only [bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero,
      core.slice.Slice.is_empty, emptyOdd, decide_true, bind_ok, ite_true, true_or]
  · by_cases emptyIds : ids.length = 0
    · simp only [bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero,
        core.slice.Slice.is_empty, emptyOdd, emptyIds, decide_true, decide_false, bind_ok,
        Bool.false_eq_true, ite_false, ite_true, or_true]
    · simp only [bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero,
        core.slice.Slice.is_empty, emptyOdd, emptyIds, decide_false, bind_ok,
        Bool.false_eq_true, ite_false, false_or, bits, bne_self_eq_false]

/-- The rebuilt verifier's 18-ID seed follows the tile path, not insert_18.
The tile body itself remains the explicit typed slot. -/
theorem public_degree_18_seed_route (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch) (tile : Tile)
    (odd ids result : Slice U64) (out : odd.length = 18) (count : ids.length = 18)
    (called : tile 4#usize false odd ids = .ok result) :
    bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
      one18 one32 single sparse tile gf64 odd ids = .ok result := by
  have dispatched := public_dispatch_refines one18 one32 single sparse tile odd ids
  rw [ite_eq_right (by omega : ¬ (odd.length = 0 ∨ ids.length = 0))] at dispatched
  rw [dispatched]
  exact free_large_single_tile one18 one32 single sparse tile odd ids result (by omega) (by omega) (by omega) called

/-- The public capacity-18 single-ID path binds its exact verified original
leaf, with the actual immutable table and original basis lookup. -/
def ActualPublicSingle18 : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
  ∀ (one32 : Single) (single : SingleCapacity) (sparse : Batch) (tile : Tile)
    (odd ids : Slice U64), odd.length = 18 → ids.length = 1 →
    ∃ output,
      bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
        (insert_18 (single_bases INSERT_BASES loadModel) loadModel storeModel)
        one32 single sparse tile gf64 odd ids = .ok output ∧
      output.length = 18 ∧
      ∀ i : Fin 18, toField output[i.val]!.bv = toField odd[i.val]!.bv + toField ids[0]!.bv ^ (2 * i.val + 1)

theorem public_single18_refines : ActualPublicSingle18 := by
  intro loadModel storeModel loadLaw storeLaw one32 single sparse tile odd ids width count
  let one18 := insert_18 (single_bases INSERT_BASES loadModel) loadModel storeModel
  have method := public_dispatch_refines one18 one32 single sparse tile odd ids
  rw [ite_eq_right (by omega : ¬(odd.length = 0 ∨ ids.length = 0)),
    free_single_18 one18 one32 single sparse tile odd ids width count] at method
  obtain ⟨output, normal, length, field, _⟩ :=
    AvxInsert18.static_insert_refines loadModel storeModel loadLaw storeLaw odd ids[0]! (by omega)
  exact ⟨output, method.trans normal, length.trans width, field⟩

end BulksketchBridge.AvxInsertDispatch
