import BulksketchBridge.AvxInsertGeneral
import BulksketchBridge.AvxTileOddSum
import BulksketchBridge.PortableRebuiltSeed

namespace BulksketchBridge.AvxRebuiltSeed

open Aeneas Aeneas.Std Algebra.Gf64 DenseCoefficient RebuiltLfsr
open Aeneas.Std.AvxSquareRuntime Aeneas.Std.AvxInsertDispatchRuntime Aeneas.Std.AvxHornerChunkRuntime
open AvxInsertDispatch AvxInsertGeneral AvxTileChunkSum
open bulksketch.backend.x86_vpclmul512
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels (insert_nonzero)

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- The rebuilt verifier uses at most one output word per supplied root.
For this source shape, singleton capacities and the sparse branch are
unreachable. The exact public dispatch is empty or the original tile fold. -/
theorem rebuilt_tile_route (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch) (tile : Tile)
    (odd ids : Slice U64) (shape : odd.length ≤ ids.length) :
    insert_nonzero one18 one32 single sparse tile gf64 odd ids =
      if odd.length = 0 then .ok odd else foldTiles tile ids 0 odd := by
  rw [public_dispatch_refines]
  by_cases empty : odd.length = 0
  · simp only [empty, eq_self, true_or, ite_true]
  · have idsNonempty : ids.length ≠ 0 := by omega
    rw [ite_eq_right (fun h => h.elim empty idsNonempty), ite_eq_right empty,
      free_refines one18 one32 single sparse tile odd ids, freeDispatch,
      ite_eq_right (fun h => h.elim empty idsNonempty)]
    by_cases one : ids.length = 1
    · have width : odd.length = 1 := by omega
      rw [ite_eq_left one, width]
      simp only [batchDispatch, one, show (1 : Nat) ≤ 4 by decide, ite_true, width]
    · rw [ite_eq_right one, batchDispatch]
      by_cases few : ids.length ≤ 4
      · rw [ite_eq_left few]
        have width : odd.length = 1 ∨ odd.length = 2 ∨ odd.length = 3 ∨ odd.length = 4 := by omega
        rcases width with h | h | h | h <;> rw [h] <;> rfl
      · rw [ite_eq_right few]

private theorem selected_tile_words (load : Load) (loadLaw : AvxSquare.LoadLaw load)
    (odd ids : Slice U64) (output : 0 < odd.length) (room : ids.length ≤ 32) :
    ∃ written, selectTile (insert_tile load) odd ids = .ok written ∧ written.length = odd.length ∧
      ∀ row < odd.length,
        toField written[row]!.bv = toField odd[row]!.bv + (ids.val.map (oddPower row)).sum := by
  unfold selectTile
  by_cases small : ids.length ≤ 8
  · rw [ite_eq_left small]
    exact AvxTileOddSum.native_tile_odd_sums load loadLaw 1#usize true odd ids output (by simpa using small)
  · rw [ite_eq_right small]
    by_cases middle : ids.length ≤ 16
    · rw [ite_eq_left middle]
      exact AvxTileOddSum.native_tile_odd_sums load loadLaw 2#usize true odd ids output (by simpa using middle)
    · rw [ite_eq_right middle]
      exact AvxTileOddSum.native_tile_odd_sums load loadLaw 4#usize false odd ids output (by simpa using room)

/-- Every original tile chunk contributes the odd powers of exactly its
own input IDs. The fold preserves the original output width. -/
theorem fold_tiles_odd_sums (load : Load) (loadLaw : AvxSquare.LoadLaw load)
    (ids : Slice U64) (offset : Nat) (odd : Slice U64) (output : 0 < odd.length) :
    ∃ written, foldTiles (insert_tile load) ids offset odd = .ok written ∧ written.length = odd.length ∧
      ∀ row < odd.length, toField written[row]!.bv =
        toField odd[row]!.bv + ((ids.val.drop offset).map (oddPower row)).sum := by
  suffices ∀ fuel offset (odd : Slice U64), ids.length - offset = fuel → 0 < odd.length →
      ∃ written, foldTiles (insert_tile load) ids offset odd = .ok written ∧ written.length = odd.length ∧
        ∀ row < odd.length, toField written[row]!.bv =
          toField odd[row]!.bv + ((ids.val.drop offset).map (oddPower row)).sum by
    exact this _ offset odd rfl output
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro offset odd measure positive
    by_cases active : offset < ids.length
    · let stop := min (offset + 32) ids.length
      let part := window ids offset stop
      have partLength : part.length = stop - offset := by
        simp only [part, window, Slice.length, Slice.from_val, List.slice_length]
        apply Nat.min_eq_right
        have bounded : stop ≤ ids.length := Nat.min_le_right ..
        exact Nat.sub_le_sub_right bounded offset
      have next : offset < stop := by
        exact Nat.lt_min.mpr ⟨by omega, active⟩
      have parts : part.val ++ ids.val.drop stop = ids.val.drop offset := by
        simp only [part, window, Slice.from_val, List.slice]
        have join : offset + (stop - offset) = stop := by omega
        have dropped : (ids.val.drop offset).drop (stop - offset) = ids.val.drop stop := by
          rw [List.drop_drop, join]
        rw [← dropped, List.take_append_drop]
      obtain ⟨intermediate, selected, middleLen, first⟩ :=
        selected_tile_words load loadLaw odd part positive (by rw [partLength]; unfold stop; omega)
      obtain ⟨written, rest, finalLen, later⟩ :=
        ih (ids.length - stop) (by omega) stop intermediate rfl (by omega)
      refine ⟨written, ?_, finalLen.trans middleLen, ?_⟩
      · rw [foldTiles, dite_eq_left active]
        change (do
          let next ← selectTile (insert_tile load) odd part
          foldTiles (insert_tile load) ids stop next) = _
        rw [selected, bind_tc_ok]
        exact rest
      · intro row inRange
        rw [later row (by rwa [middleLen]), first row inRange, add_assoc, ← List.sum_append,
          ← List.map_append, parts]
    · rw [foldTiles, dite_eq_right active]
      refine ⟨odd, rfl, rfl, ?_⟩
      intro row _
      have empty : ids.val.drop offset = [] := List.drop_eq_nil_of_le (by change ids.length ≤ offset; omega)
      rw [empty]
      simp

/-- The original public AVX seed produces every rebuilt odd-syndrome word,
for all input degrees and seed lengths admitted by the verifier. -/
def ActualNativeAvxRebuiltSeed : Prop :=
  ∀ (load : Load), AvxSquare.LoadLaw load →
    ∀ (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch) (shape roots : Slice U64),
      shape.length ≤ roots.length → roots.val.Nodup →
      ∃ seed : Slice U64,
        insert_nonzero one18 one32 single sparse (insert_tile load) gf64 (zeroWords shape) roots = .ok seed ∧
        seed.length = shape.length ∧
        ∀ row < seed.length, toField seed[row]!.bv = Reconciliation.oddSyndrome (rootSupport roots) row

theorem native_avx_rebuilt_seed : ActualNativeAvxRebuiltSeed := by
  classical
  intro load loadLaw one18 one32 single sparse shape roots width distinct
  have zeroLength : (zeroWords shape).length = shape.length := by simp
  rw [rebuilt_tile_route one18 one32 single sparse (insert_tile load) (zeroWords shape) roots (by omega)]
  by_cases empty : shape.length = 0
  · rw [ite_eq_left (zeroLength.trans empty)]
    exact ⟨zeroWords shape, rfl, zeroLength, fun row inSeed => (by omega : False).elim⟩
  · have nonempty : 0 < (zeroWords shape).length := by omega
    rw [ite_eq_right (by omega : (zeroWords shape).length ≠ 0)]
    obtain ⟨seed, ran, len, meaning⟩ := fold_tiles_odd_sums load loadLaw roots 0 (zeroWords shape) nonempty
    refine ⟨seed, ran, len.trans zeroLength, ?_⟩
    intro row inSeed
    have inside : row < shape.length := by omega
    have zero : (zeroWords shape)[row]! = 0#u64 := by simp [zeroWords, inside]
    rw [meaning row (by omega), zero]
    simp only [show (0#u64).bv = 0 from rfl, toField_zero, zero_add, List.drop_zero]
    have injective : Function.Injective (fun word : U64 => toField word.bv) :=
      fun left right equal => U64.bv_eq_imp_eq left right (toField_injective equal)
    simp only [Reconciliation.oddSyndrome, Reconciliation.powerSum, rootSupport]
    rw [List.sum_toFinset _ (distinct.map injective), List.map_map]
    rfl

#print axioms rebuilt_tile_route
#print axioms fold_tiles_odd_sums
#print axioms native_avx_rebuilt_seed

end BulksketchBridge.AvxRebuiltSeed
