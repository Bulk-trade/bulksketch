import BulksketchBridge.AvxTileSyndrome

namespace BulksketchBridge.AvxTileChunkSum

open Aeneas.Std Algebra.Gf64 AvxTileSyndrome
open scoped BigOperators

noncomputable def oddPower (row : Nat) (id : U64) : Field :=
  toField id.bv ^ (2 * row + 1)

theorem chunk_sum (chunk : Slice U64) (bound : chunk.length ≤ 8) (row : Nat) :
    (∑ lane : Fin 8, if lane.val < chunk.length then oddPower row chunk[lane.val]! else 0) =
      (chunk.val.map (oddPower row)).sum := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ lane ∈ Finset.range 8, if lane < chunk.length then oddPower row chunk[lane]! else 0 := by
      apply Finset.sum_congr rfl
      intro lane inside
      rw [dite_eq_left (Finset.mem_range.mp inside)]
    _ = ∑ lane ∈ Finset.range chunk.length, oddPower row chunk[lane]! := by
      rw [← Finset.sum_filter]
      congr 1
      ext lane
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    _ = (chunk.val.map (oddPower row)).sum := by
      conv_rhs => rw [← List.ofFn_getElem (xs := chunk.val), List.map_ofFn, List.sum_ofFn,
        Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro lane inside
      have h : lane < chunk.val.length := Finset.mem_range.mp inside
      rw [dite_eq_left h]
      change oddPower row chunk[lane]! = oddPower row chunk.val[lane]
      apply congrArg (oddPower row)
      rw [Slice.getElem!_Nat_eq]
      exact (List.Inhabited_getElem_eq_getElem! _ _ h).symm

theorem row_partition (chunks : List (Slice U64)) (fits : ∀ chunk ∈ chunks, chunk.length ≤ 8)
    (row : Nat) :
    toField (AvxHorizontalXor.parity
      (reduceTile (chunks.map (fun chunk => step (AvxSquare.loadWords chunk) row)))) =
      ((chunks.flatMap (fun chunk => chunk.val)).map (oddPower row)).sum := by
  rw [loaded_row_field]
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append]
    rw [show (fun lane : Fin 8 =>
      if lane.val < chunk.length then toField chunk[lane.val]!.bv ^ (2 * row + 1) else 0) =
      (fun lane : Fin 8 => if lane.val < chunk.length then oddPower row chunk[lane.val]! else 0) from rfl,
      chunk_sum chunk (fits chunk (by simp)) row]
    exact congrArg ((chunk.val.map (oddPower row)).sum + ·) (ih (by
      intro item member
      exact fits item (List.mem_cons_of_mem _ member)))


private def firstChunk (ids : Slice U64) : Slice U64 :=
  Slice.from (ids.val.take 8) (by
    rw [List.length_take]
    exact (Nat.min_le_right 8 ids.val.length).trans ids.length_ineq)

private def remainingChunks (ids : Slice U64) : Slice U64 :=
  Slice.from (ids.val.drop 8) (by
    rw [List.length_drop]
    exact (Nat.sub_le ..).trans ids.length_ineq)

def tileChunks (ids : Slice U64) : Nat → List (Slice U64)
  | 0 => []
  | width + 1 => firstChunk ids :: tileChunks (remainingChunks ids) width

theorem tile_chunks_fit (ids : Slice U64) (width : Nat) :
    ∀ chunk ∈ tileChunks ids width, chunk.length ≤ 8 := by
  induction width generalizing ids with
  | zero => simp [tileChunks]
  | succ width ih =>
    intro chunk member
    simp only [tileChunks, List.mem_cons] at member
    rcases member with rfl | tail
    · simp only [firstChunk, Slice.length, Slice.from_val, List.length_take]
      exact Nat.min_le_left _ _
    · exact ih _ _ tail

theorem tile_chunks_partition (ids : Slice U64) (width : Nat) (fits : ids.length ≤ 8 * width) :
    (tileChunks ids width).flatMap (fun chunk => chunk.val) = ids.val := by
  induction width generalizing ids with
  | zero =>
    have empty : ids.val.length = 0 := by
      change ids.val.length ≤ 8 * 0 at fits
      omega
    simp [tileChunks, List.length_eq_zero_iff.mp empty]
  | succ width ih =>
    simp only [tileChunks, List.flatMap_cons]
    rw [ih (remainingChunks ids)]
    · simp only [firstChunk, remainingChunks, Slice.from_val]
      exact List.take_append_drop _ _
    · simp only [remainingChunks, Slice.length, Slice.from_val, List.length_drop]
      change ids.val.length ≤ 8 * (width + 1) at fits
      omega

/-- The modeled masked-load and register recurrence covers all tile IDs,
    including the partial final chunk and zero padding lanes. -/
def ActualTileRowMath : Prop :=
  ∀ (ids : Slice U64) (width : Nat), ids.length ≤ 8 * width → ∀ row : Nat,
    toField (AvxHorizontalXor.parity
      (reduceTile ((tileChunks ids width).map (fun chunk => step (AvxSquare.loadWords chunk) row)))) =
      (ids.val.map (oddPower row)).sum

theorem tile_row_exact : ActualTileRowMath := by
  intro ids width fits row
  rw [row_partition _ (tile_chunks_fit ids width), tile_chunks_partition ids width fits]

#print axioms tile_row_exact

end BulksketchBridge.AvxTileChunkSum
