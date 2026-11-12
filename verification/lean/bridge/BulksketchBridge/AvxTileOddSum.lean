import BulksketchBridge.AvxTileOutputMath
import BulksketchBridge.AvxTileChunkSum

namespace BulksketchBridge.AvxTileOddSum

open Aeneas Aeneas.Std Algebra.Gf64 Result
open Aeneas.Std.Avx512Register
open BulksketchBridge.AvxTileInitMath BulksketchBridge.AvxTileChunkSum
open BulksketchBridge.AvxTileNative BulksketchBridge.AvxTileRowMath
open BulksketchBridge.AvxTileOutputMath BulksketchBridge.AvxTileSyndrome
open BulksketchBridge.AvxTileSyndromeLoop
open BulksketchBridge.Avx512RegisterChallenges
open bulksketch.backend.x86_vpclmul512

set_option maxHeartbeats 2600000

def bases (W : Usize) (ids : Slice U64) : List Word512 :=
  (tileChunks ids W.val).map AvxSquare.loadWords

private theorem suffix_exact (odd : Slice U64) (room : 1 ≤ odd.length) :
    indexTail odd = .ok (dropIds odd 1, fun replacement => odd.setSlice! 1 replacement.val) := by
  unfold indexTail
  rw [Slice.index_mut_SliceIndexRangeFromUsizeSliceInst]
  obtain ⟨⟨suffix, back⟩, normal, suffixValue, _, backValue⟩ := RawMulTable.normal_of_spec _ _
    (core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.step_spec ⟨1#usize⟩ odd (by exact room))
  have exactSuffix : suffix = dropIds odd 1 := by
    apply Slice.ext
    change suffix.val = odd.val.drop 1 at suffixValue
    simpa only [dropIds, Slice.from_val] using suffixValue
  have exactBack : back = fun replacement => odd.setSlice! 1 replacement.val := by
    funext replacement
    apply Slice.ext
    rw [backValue, Slice.setSlice!_val]
    rfl
  rw [normal, exactSuffix, exactBack]

/-- The complete original tile produces the scheduled register XOR for every
odd word, starting with the separately folded first row. -/
theorem native_tile_odd_rows (load : AvxSquareRuntime.Load) (law : AvxSquare.LoadLaw load)
    (W : Usize) (CL : Bool) (odd ids : Slice U64) (nonempty : 0 < odd.length) :
    ∃ written, insert_tile load W CL odd ids = .ok written ∧
      written.val = transform (bases W ids) 0 odd.val := by
  let b := bases W ids
  have initial := initialized_arrays W ids
  have firstFold := first_row_fold W ids
  cases initialPair : arraysAfterInit W ids with
  | mk powers steps =>
    rw [initialPair] at initial firstFold
    have powersExact : powers.val = b.map (fun word => step word 0) := by
      change powers.val = b.map id
      rw [List.map_id]
      exact initial.1
    have stepsExact : steps.val = b.map (fun word => productsReduced word word) := by
      unfold b bases
      rw [List.map_map]
      exact initial.2
    have first : powers.val.foldl xorRegister zero =
        reduceTile (b.map (fun word => step word 0)) := by
      change powers.val.foldl xorRegister zero = reduceTile (b.map id)
      rw [List.map_id]
      exact firstFold
    obtain ⟨head, readHead, headExact⟩ := RawMulTable.normal_of_spec _ _
      (Slice.index_usize_spec odd 0#usize (by exact nonempty))
    let updatedHead := head ^^^ rowWord b 0
    obtain ⟨odd1, writeHead, changed⟩ := RawMulTable.normal_of_spec _ _
      (Slice.update_spec odd 0#usize updatedHead (by exact nonempty))
    have length : odd1.length = odd.length := by
      rw [changed]
      simp [Slice.set, Slice.length, Slice.setAtNat]
    have suffix := suffix_exact odd1 (by omega)
    let tail := dropIds odd1 1
    let row := rowWrites zero steps tail.length ⟨tail, 0⟩ id powers
    have tailMath := row_writes_math b tail 0 (by omega) 0 id powers steps powersExact stepsExact
    have tailEq : (row.2 row.1).slice.val = transform b 1 tail.val := by
      have frame := congrArg (fun it : OddIter => it.slice.val) tailMath
      simpa only [row, Nat.sub_zero, id, outputFrame, Slice.from_val,
        List.take_zero, List.nil_append, Nat.zero_add, List.drop_zero] using frame
    refine ⟨odd1.setSlice! 1 (row.2 row.1).slice.val, ?_, ?_⟩
    · rw [native_tile_refines load law W CL odd ids, expected, initialPair]
      dsimp! only
      rw [first, readHead, bind_ok]
      change (do
        let odd1 ← Slice.update odd 0#usize updatedHead
        let (tail, restore) ← indexTail odd1
        let (output, back) := rowWrites zero steps tail.length ⟨tail, 0⟩ id powers
        .ok (restore (back output).slice)) = _
      simp only [Bind.bind, writeHead, bind_ok, suffix]
      rfl
    · rw [Slice.setSlice!_val, tailEq]
      have firstChanged : odd1.val = updatedHead :: odd.val.drop 1 := by
        rw [changed, Slice.set_val_eq]
        cases words : odd.val with
        | nil =>
          have bad : odd.length = 0 := by simp [Slice.length, words]
          omega
        | cons first rest => rfl
      have tailOriginal : tail.val = odd.val.drop 1 := by
        simp only [tail, dropIds, Slice.from_val, firstChanged, List.drop_succ_cons, List.drop_zero]
      rw [tailOriginal, firstChanged]
      have original : odd.val = head :: odd.val.drop 1 := by
        change head = odd.val[0] at headExact
        rw [headExact]
        simpa only [List.drop_zero, Nat.zero_add] using
          (List.drop_eq_getElem_cons (show 0 < odd.val.length from nonempty))
      conv_rhs => rw [original, transform]
      have takeAll : (transform b 1 odd.val.tail).take (odd.val.length - 1) =
          transform b 1 odd.val.tail := by
        apply List.take_of_length_le
        rw [transform_length, List.length_tail]
      simp [List.setSlice!, transform_length, updatedHead, b, takeAll]

/-- Every emitted register word represents the full odd-power sum over the
input IDs, under the exact native dispatcher bound on one tile. -/
theorem native_row_word_field (W : Usize) (ids : Slice U64)
    (admitted : ids.length ≤ 8 * W.val) (row : Nat) :
    toField (rowWord (bases W ids) row).bv = (ids.val.map (oddPower row)).sum := by
  have mapExact : (bases W ids).map (fun word => step word row) =
      (tileChunks ids W.val).map (fun chunk => step (AvxSquare.loadWords chunk) row) := by
    simp [bases, List.map_map]
  unfold rowWord
  rw [mapExact]
  exact tile_row_exact ids W.val admitted row

private theorem transform_word (values : List Word512) (start : Nat)
    (words : List U64) (j : Nat) (bound : j < words.length) :
    (transform values start words)[j]! = words[j]! ^^^ rowWord values (start + j) := by
  induction words generalizing start j with
  | nil => cases bound
  | cons first rest ih =>
    cases j with
    | zero => simp only [transform, List.getElem!_cons_zero, Nat.add_zero]
    | succ j =>
      simp only [transform, List.getElem!_cons_succ]
      rw [ih (start + 1) j (by simpa using bound)]
      rw [show start + 1 + j = start + (j + 1) by omega]

/-- The original single AVX tile updates every output word by the odd
syndrome of all admitted IDs, including partial tiles and padding lanes. -/
def ActualNativeTileOddSums : Prop :=
  ∀ (load : AvxSquareRuntime.Load), AvxSquare.LoadLaw load →
    ∀ (W : Usize) (CL : Bool) (odd ids : Slice U64),
    0 < odd.length → ids.length ≤ 8 * W.val →
    ∃ written, insert_tile load W CL odd ids = .ok written ∧
      written.length = odd.length ∧
      ∀ j < odd.length, toField written[j]!.bv =
        toField odd[j]!.bv + (ids.val.map (oddPower j)).sum

theorem native_tile_odd_sums : ActualNativeTileOddSums := by
  intro load law W CL odd ids nonempty fits
  obtain ⟨written, ran, exactWords⟩ := native_tile_odd_rows load law W CL odd ids nonempty
  refine ⟨written, ran, ?_, ?_⟩
  · simpa only [Slice.length, transform_length] using congrArg List.length exactWords
  · intro j bound
    rw [Slice.getElem!_Nat_eq, exactWords, transform_word (bases W ids) 0 odd.val j bound, Nat.zero_add]
    change toField (odd.val[j]!.bv ^^^ (rowWord (bases W ids) j).bv) = _
    rw [toField_xor, native_row_word_field W ids fits j, Slice.getElem!_Nat_eq]

#print axioms native_tile_odd_sums

#print axioms native_tile_odd_rows
#print axioms native_row_word_field

end BulksketchBridge.AvxTileOddSum
