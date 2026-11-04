import BulksketchBridge.MapsTables
import BulksketchBridge.RawMulAccum

/-!
Total correctness of the unchanged native16-row quadratic lookup loop.
The invariant tracks the actual slice iterator, the exact remaining input word
and the independent chunk-prefix accumulator. All casts, reads and constant
shifts are proved normal before the actual loop is unfolded.
-/

namespace BulksketchBridge.MapsQuadratic

open Aeneas Aeneas.Std

private abbrev Row := Array U64 16#usize
private abbrev Iterator := core.slice.iter.Iter Row

private def iteratorAt (count : Nat) : Iterator :=
  ⟨Array.to_slice bulksketch.field.quadratic_chunks.GF64_QUADRATIC_CHUNKS, count⟩

private def remainingWord (input : U64) (count : Nat) : U64 :=
  ⟨input.bv >>> (4 * count)⟩

private def prefixWord (input : U64) (count : Nat) : U64 :=
  ⟨BulksketchProofs.Field.Maps.chunkPrefix input.bv count⟩

private theorem sixteen_val : (16#usize).val = 16 := by simp

private theorem iterator_length (count : Nat) : (iteratorAt count).slice.val.length = 16 := by
  simp only [iteratorAt, Array.to_slice, Slice.from_val, Array.property]
  rfl

private theorem iterator_next (count : Nat) (small : count < 16) :
    ∃ row : Row,
      core.slice.iter.IteratorSliceIter.next (iteratorAt count) =
        Result.ok (some row, iteratorAt (count + 1)) ∧
      row.val.map (fun word => word.bv) =
        ((BulksketchProofs.Field.Maps.chunks[count]?).getD []) := by
  have bound : count < (iteratorAt count).slice.val.length := by
    rw [iterator_length]
    exact small
  have active : (iteratorAt count).i < (iteratorAt count).slice.len := by
    change count < (iteratorAt count).slice.len.val
    simpa only [Slice.len_val, Slice.length] using bound
  refine ⟨(iteratorAt count).slice[count]'bound, ?_, ?_⟩
  · simp only [core.slice.iter.IteratorSliceIter.next, active, _root_.dite_true]
    rfl
  · have sourceEq :
        bulksketch.field.quadratic_chunks.GF64_QUADRATIC_CHUNKS.val.map
          (fun row => row.val.map (fun word => word.bv)) =
            BulksketchProofs.Field.Maps.chunks := MapsTables.chunks_match_source
    have actualBound : count <
        bulksketch.field.quadratic_chunks.GF64_QUADRATIC_CHUNKS.val.length := by
      simpa only [iteratorAt, Array.to_slice, Slice.from_val] using bound
    have selected := congrArg
      (fun rows : List (List (BitVec 64)) => (rows[count]?).getD []) sourceEq
    simp only [List.getElem?_map, List.getElem?_eq_getElem actualBound,
      Option.map_some, Option.getD_some] at selected
    change ((iteratorAt count).slice.val[count]'bound).val.map (fun word => word.bv) = _
    have listEq : (iteratorAt count).slice.val =
        bulksketch.field.quadratic_chunks.GF64_QUADRATIC_CHUNKS.val := by
      simp only [iteratorAt, Array.val_to_slice]
    simpa only [listEq] using selected

private theorem pointer_range : 15 ≤ UScalar.max .Usize := by
  simp only [UScalar.max, UScalarTy.numBits]
  rcases System.Platform.numBits_eq with width | width
  · rw [width]
    decide
  · rw [width]
    decide

/-- Every source low-nibble conversion is inner Ok on both supported usize widths. -/
theorem masked_conversion_normal (word : U64) :
    Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from (word &&& 15#u64) =
      Result.ok (.Ok (UScalar.cast .Usize (word &&& 15#u64))) := by
  have bounded : (word &&& 15#u64).val ≤ 15 := by
    change (word.bv &&& (15 : BitVec 64)).toNat ≤ 15
    rw [BitVec.toNat_and]
    exact Nat.and_le_right
  have inRange := Nat.le_trans bounded pointer_range
  simp only [Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from,
    core.num.tryFromUScalar, inRange, ite_true]

private theorem array_lookup_bits (row : Row) (index : Usize) (small : index.val < 16) :
    Array.index_usize row index =
      Result.ok (⟨((row.val.map (fun word => word.bv))[index.val]?).getD 0⟩ : U64) := by
  have bound : index.val < row.val.length := by
    simpa only [Array.property, sixteen_val] using small
  simp only [Array.index_usize, Array.getElem?_Usize_eq, List.getElem?_eq_getElem bound,
    List.getElem?_map, Option.map_some, Option.getD_some]

private theorem chunk_lookup (input : U64) (count : Nat) (small : count < 16)
    (row : Row)
    (rowBits : row.val.map (fun word => word.bv) =
      (BulksketchProofs.Field.Maps.chunks[count]?).getD []) :
    Array.index_usize row (UScalar.cast .Usize (RawMulAccum.nibbleWord input count)) =
      Result.ok (⟨BulksketchProofs.Field.Maps.chunkValue count
        ((input.bv >>> (4 * count)).setWidth 4)⟩ : U64) := by
  have bounds := RawMulAccum.nibble_bounds input count small
  have indexSmall := bounds.2.2.1
  have indexEq := congrArg (fun value : BitVec 4 => value.toNat) bounds.2.2.2.2
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexSmall] at indexEq
  rw [array_lookup_bits row _ indexSmall]
  apply congrArg Result.ok
  apply U64.bv_eq_imp_eq
  change ((row.val.map (fun word => word.bv))[_]?).getD 0 = _
  rw [rowBits, indexEq]
  rfl

private theorem remaining_shift (input : U64) (count : Nat) :
    remainingWord input count >>> (4#i32) =
      Result.ok (remainingWord input (count + 1)) := by
  change Result.ok (⟨(input.bv >>> (4 * count)) >>> (4 : Nat)⟩ : U64) = _
  apply congrArg Result.ok
  apply U64.bv_eq_imp_eq
  change (input.bv >>> (4 * count)) >>> (4 : Nat) = input.bv >>> (4 * (count + 1))
  rw [← BitVec.shiftRight_add]
  congr 1

/-- Each unchanged body consumes exactly one row and four input bits, and all
checked conversions, table reads and constant shifts return normally. -/
theorem body_step (input : U64) (count : Nat) (small : count < 16) :
    bulksketch.field.maps.quadratic_value_loop0.body
      (iteratorAt count) (remainingWord input count) (prefixWord input count) =
        Result.ok (ControlFlow.cont
          (iteratorAt (count + 1), remainingWord input (count + 1), prefixWord input (count + 1))) := by
  obtain ⟨row, nextNormal, rowBits⟩ := iterator_next count small
  simp only [bulksketch.field.maps.quadratic_value_loop0.body, nextNormal, bind_ok,
    lift, masked_conversion_normal, core.result.Result.expect]
  change (do
    let entry ← Array.index_usize row (UScalar.cast .Usize (RawMulAccum.nibbleWord input count))
    let remaining ← remainingWord input count >>> (4#i32)
    Result.ok (ControlFlow.cont
      (iteratorAt (count + 1), remaining, prefixWord input count ^^^ entry))) = _
  rw [chunk_lookup input count small row rowBits]
  simp only [Bind.bind, bind_ok, remaining_shift]
  rfl

private theorem iterator_terminal :
    core.slice.iter.IteratorSliceIter.next (iteratorAt 16) =
      Result.ok (none, iteratorAt 16) := by
  have inactive : ¬ (iteratorAt 16).i < (iteratorAt 16).slice.len := by
    change ¬ 16 < (iteratorAt 16).slice.len.val
    simp only [Slice.len_val, Slice.length, iterator_length, Nat.lt_irrefl, not_false_eq_true]
  simp only [core.slice.iter.IteratorSliceIter.next, inactive, _root_.dite_false]

/-- Exhaustion is tested before any read or shift is attempted. -/
theorem terminal_body (input : U64) :
    bulksketch.field.maps.quadratic_value_loop0.body
      (iteratorAt 16) (remainingWord input 16) (prefixWord input 16) =
        Result.ok (ControlFlow.done (expectedChunkWord input)) := by
  simp only [bulksketch.field.maps.quadratic_value_loop0.body, iterator_terminal, bind_ok]
  rfl

/-- Every valid original source-loop suffix terminates with the complete16-chunk value. -/
theorem every_prefix_completes (input : U64) (count : Nat) (bounded : count ≤ 16) :
    bulksketch.field.maps.quadratic_value_loop0 (iteratorAt count)
      (remainingWord input count) (prefixWord input count) =
        Result.ok (expectedChunkWord input) := by
  suffices ∀ remaining count, count ≤ 16 → 16 - count = remaining →
      bulksketch.field.maps.quadratic_value_loop0 (iteratorAt count)
        (remainingWord input count) (prefixWord input count) =
          Result.ok (expectedChunkWord input) from
    this (16 - count) count bounded rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro count bounded remainingEq
    by_cases terminal : count = 16
    · subst count
      unfold bulksketch.field.maps.quadratic_value_loop0
      unfold loop
      dsimp only
      rw [terminal_body input]
      simp only [bind_ok]
    · have small : count < 16 := by omega
      have recursive := ih (16 - (count + 1)) (by omega) (count + 1) (by omega) rfl
      unfold bulksketch.field.maps.quadratic_value_loop0
      unfold loop
      dsimp only
      rw [body_step input count small]
      simp only [bind_ok]
      exact recursive

/-- The real Gf64 instance initializes and completes every source chunk contribution. -/
theorem quadratic_value_refines : MapsQuadraticChallenges.actualValueMatchesAllChunkContributions := by
  intro input
  simp only [bulksketch.field.maps.quadratic_value,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS,
    bind_ok, ite_true, SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
  have complete := every_prefix_completes input 0 (by decide)
  have inputEta : (⟨input.bv⟩ : U64) = input := by
    apply U64.bv_eq_imp_eq
    rfl
  have zeroWord : (⟨(0 : BitVec 64)⟩ : U64) = 0#u64 := by
    apply U64.bv_eq_imp_eq
    simp
  simpa only [iteratorAt, Array.to_slice, remainingWord, prefixWord, BulksketchProofs.Field.Maps.chunkPrefix,
    Nat.mul_zero, BitVec.ushiftRight_zero, inputEta, zeroWord] using complete

end BulksketchBridge.MapsQuadratic
