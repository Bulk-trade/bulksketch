import BulksketchBridge.AvxTileNative
import BulksketchBridge.AvxTileChunkSum

namespace BulksketchBridge.AvxTileInitMath

open Aeneas Aeneas.Std
open Aeneas.Std.Avx512Register Aeneas.Std.AvxTileRuntime Aeneas.Std.AvxHornerChunkRuntime
open BulksketchBridge.AvxTileInit BulksketchBridge.AvxTileNative
open BulksketchBridge.AvxTileDoubleZip BulksketchBridge.AvxTileChunkSum
open BulksketchBridge.Avx512RegisterChallenges

set_option maxHeartbeats 2200000

def dropIds (words : Slice U64) (offset : Nat) : Slice U64 :=
  Slice.from (words.val.drop offset) (by
    rw [List.length_drop]
    exact (Nat.sub_le ..).trans words.length_ineq)

def takeIds (words : Slice U64) : Slice U64 :=
  Slice.from (words.val.take 8) (by
    rw [List.length_take]
    exact (Nat.min_le_right ..).trans words.length_ineq)

def squareChunk (words : Slice U64) : Word512 :=
  productsReduced (AvxSquare.loadWords words) (AvxSquare.loadWords words)

theorem chunk_eq_take (state : Init) (width : state.snd.width = 8) :
    chunk state = takeIds (dropIds state.snd.words state.snd.offset) := by
  apply Slice.ext
  simp only [chunk, window, stop, width, takeIds, dropIds, Slice.from_val, List.slice]
  have len : min (state.snd.offset + 8) state.snd.words.length - state.snd.offset =
      min 8 (state.snd.words.val.drop state.snd.offset).length := by
    rw [List.length_drop]
    change min (state.snd.offset + 8) state.snd.words.val.length - state.snd.offset =
      min 8 (state.snd.words.val.length - state.snd.offset)
    omega
  rw [len]
  by_cases short : (state.snd.words.val.drop state.snd.offset).length ≤ 8
  · rw [Nat.min_eq_right short, List.take_length, List.take_of_length_le short]
  · rw [Nat.min_eq_left (by omega)]

theorem after_drop (state : Init) (width : state.snd.width = 8) :
    dropIds (advance state).snd.words (advance state).snd.offset =
      dropIds (dropIds state.snd.words state.snd.offset) 8 := by
  apply Slice.ext
  simp only [advance, dropIds, stop, width, Slice.from_val, List.drop_drop]
  by_cases short : state.snd.words.length ≤ state.snd.offset + 8
  · rw [Nat.min_eq_right short, List.drop_eq_nil_of_le (by rfl : state.snd.words.val.length ≤ state.snd.words.length),
      List.drop_eq_nil_of_le short]
  · rw [Nat.min_eq_left (by omega)]

theorem chunks_cons (ids : Slice U64) (width : Nat) :
    tileChunks ids (width + 1) = takeIds ids :: tileChunks (dropIds ids 8) width := rfl

theorem empty_power (words : Slice U64) (empty : words.val = []) :
    AvxSquare.loadWords words = zero := by
  funext pair high
  have length : words.length = 0 := by simp [Slice.length, empty]
  simp [AvxSquare.loadWords, zero, length]

theorem zero_square : productsReduced zero zero = zero := by
  funext pair high
  change Algebra.Gf64.multiplyWord 0 0 = 0
  apply Algebra.Gf64.toField_injective
  rw [Algebra.Gf64.toField_mul, Algebra.Gf64.toField_zero, zero_mul]

theorem padded_empty (words : Slice U64) (empty : words.val = []) (width : Nat) :
    (tileChunks words width).map AvxSquare.loadWords = List.replicate width zero ∧
    (tileChunks words width).map squareChunk = List.replicate width zero := by
  induction width generalizing words with
  | zero => exact ⟨rfl, rfl⟩
  | succ width ih =>
    have first : (takeIds words).val = [] := by simp [takeIds, empty]
    have tail : (dropIds words 8).val = [] := by simp [dropIds, empty]
    obtain ⟨powers, steps⟩ := ih _ tail
    rw [chunks_cons]
    simp only [List.map_cons, List.replicate_succ, powers, steps, empty_power _ first,
      squareChunk, zero_square, and_self]

private theorem write_prefix (position : Nat) (tail : List Word512) (value : Word512) :
    (List.replicate (position + 1) zero ++ tail).set position value =
      List.replicate position zero ++ value :: tail := by
  rw [List.replicate_succ', List.append_assoc]
  simp only [List.singleton_append]
  rw [List.set_append_right position value (by simp), List.length_replicate, Nat.sub_self]
  rfl

/-- Both independent mutable Zip writebacks produce the padded tile from
the exact remaining ID cursor. Earlier slots stay unchanged at zero. -/
theorem init_payloads (fuel : Nat) (state : Init) (position : Nat)
    (sameLeft : state.fst.fst.i = position) (sameRight : state.fst.snd.i = position)
    (zeroLeft : state.fst.fst.slice.val = List.replicate (position + fuel) zero)
    (zeroRight : state.fst.snd.slice.val = List.replicate (position + fuel) zero)
    (width : state.snd.width = 8) :
    let chunks := tileChunks (dropIds state.snd.words state.snd.offset) fuel
    (initWrites fuel state).2.fst.fst.slice.val =
      List.replicate position zero ++ chunks.map AvxSquare.loadWords ∧
    (initWrites fuel state).1.fst.snd.slice.val =
      List.replicate position zero ++ chunks.map squareChunk := by
  induction fuel generalizing state position with
  | zero =>
    simp only [initWrites, tileChunks, List.map_nil, List.append_nil, Nat.add_zero] at *
    exact ⟨zeroLeft, zeroRight⟩
  | succ fuel ih =>
    have leftSize : state.fst.fst.slice.length = position + (fuel + 1) := by
      simp [Slice.length, zeroLeft]
    have rightSize : state.fst.snd.slice.length = position + (fuel + 1) := by
      simp [Slice.length, zeroRight]
    by_cases exhausted : state.snd.words.length ≤ state.snd.offset
    · have done : ¬active state := fun more => (Nat.not_lt.mpr exhausted) more.2.2
      have noWords : (dropIds state.snd.words state.snd.offset).val = [] := by
        simp [dropIds, List.drop_eq_nil_of_le exhausted]
      obtain ⟨powers, steps⟩ := padded_empty _ noWords (fuel + 1)
      simp only [initWrites, ite_eq_right done, zeroLeft, zeroRight, powers, steps, List.replicate_add, and_self]
    · have more : active state := ⟨by omega, by omega, Nat.lt_of_not_ge exhausted⟩
      obtain ⟨powers, steps⟩ := ih (advance state) (position + 1)
        (by simp [advance, sameLeft]) (by simp [advance, sameRight])
        (by simpa only [advance, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using zeroLeft)
        (by simpa only [advance, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using zeroRight) width
      simp only [initWrites, ite_eq_left more]
      cases final : initWrites fuel (advance state) with
      | mk stepsState powersState =>
        rw [final] at powers steps
        simp only [Prod.fst, Prod.snd] at powers steps
        have tailWords := after_drop state width
        have here := chunk_eq_take state width
        change powersState.fst.fst.slice.val = _ at powers
        change stepsState.fst.snd.slice.val = _ at steps
        simp only [writePower, writeStep, overwrite, Slice.setAtNat, Slice.from_val, sameLeft, sameRight,
          powers, steps, tailWords, here, chunks_cons, List.map_cons, squareChunk]
        rw [write_prefix, write_prefix]
        exact ⟨rfl, rfl⟩

theorem tile_chunks_length (ids : Slice U64) (width : Nat) :
    (tileChunks ids width).length = width := by
  induction width generalizing ids with
  | zero => rfl
  | succ width ih => simp only [chunks_cons, List.length_cons, ih]

/-- The actual initialization leaves the padded chunks in the power array
and their exact field squares in the step array. -/
theorem initialized_arrays (W : Usize) (ids : Slice U64) :
    (arraysAfterInit W ids).1.val = (tileChunks ids W.val).map AvxSquare.loadWords ∧
    (arraysAfterInit W ids).2.val = (tileChunks ids W.val).map squareChunk := by
  let initial := initState W ids
  have remainingWidth : remaining initial = W.val := by
    simp [remaining, initial, initState, Array.to_slice, Slice.length]
  have left : initial.fst.fst.slice.val = List.replicate W.val zero := by
    simp [initial, initState, Array.repeat, Array.to_slice]
  have right : initial.fst.snd.slice.val = List.replicate W.val zero := left
  obtain ⟨powers, steps⟩ := init_payloads W.val initial 0 rfl rfl
    (by simpa using left) (by simpa using right) rfl
  have dropZero : dropIds initial.snd.words initial.snd.offset = ids := by
    apply Slice.ext
    simp [initial, initState, dropIds]
  rw [dropZero] at powers steps
  simp only [List.replicate_zero, List.nil_append] at powers steps
  generalize result : initWrites W.val initial = written
  rcases written with ⟨writtenSteps, writtenPowers⟩
  rw [result] at powers steps
  change writtenPowers.fst.fst.slice.val = _ at powers
  change writtenSteps.fst.snd.slice.val = _ at steps
  let original := Array.repeat W zero
  have out : arraysAfterInit W ids =
      (original.from_slice writtenPowers.fst.fst.slice, original.from_slice writtenSteps.fst.snd.slice) := by
    unfold arraysAfterInit
    change (let (afterSteps, afterPowers) := initWrites (remaining initial) initial
            (original.from_slice afterPowers.fst.fst.slice, original.from_slice afterSteps.fst.snd.slice)) = _
    rw [remainingWidth, result]
  have powersLen : writtenPowers.fst.fst.slice.val.length = W.val := by
    rw [powers, List.length_map, tile_chunks_length]
  have stepsLen : writtenSteps.fst.snd.slice.val.length = W.val := by
    rw [steps, List.length_map, tile_chunks_length]
  rw [out]
  exact ⟨(Array.from_slice_val original writtenPowers.fst.fst.slice powersLen).trans powers,
    (Array.from_slice_val original writtenSteps.fst.snd.slice stepsLen).trans steps⟩

#print axioms init_payloads
#print axioms initialized_arrays

end BulksketchBridge.AvxTileInitMath
