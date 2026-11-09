import BulksketchBridge.AvxTileInitMath
import BulksketchBridge.AvxTilePowerMath

namespace BulksketchBridge.AvxTileRowMath

open Aeneas Aeneas.Std Algebra.Gf64
open Aeneas.Std.Avx512Register
open BulksketchBridge.Avx512RegisterChallenges BulksketchBridge.AvxTileSyndrome
open BulksketchBridge.AvxTileNative BulksketchBridge.AvxTileSyndromeLoop
open BulksketchBridge.AvxTilePowerLoop BulksketchBridge.AvxTilePowerMath
open BulksketchBridge.AvxTileInitMath

set_option maxHeartbeats 2200000

theorem xor_zero_right (word : Word512) : xorRegister word zero = word := by
  funext pair high
  simp [xorRegister, zero]

theorem xor_zero_left (word : Word512) : xorRegister zero word = word := by
  funext pair high
  simp [xorRegister, zero]

theorem xor_assoc (a b c : Word512) :
    xorRegister (xorRegister a b) c = xorRegister a (xorRegister b c) := by
  funext pair high
  exact BitVec.xor_assoc ..

theorem fold_registers (words : List Word512) (initial : Word512) :
    words.foldl xorRegister initial = xorRegister initial (reduceTile words) := by
  induction words generalizing initial with
  | nil => exact (xor_zero_right _).symm
  | cons word rest ih =>
    simp only [List.foldl_cons, reduceTile, ih, xor_assoc]

theorem fold_registers_zero (words : List Word512) :
    words.foldl xorRegister zero = reduceTile words :=
  (fold_registers _ _).trans (xor_zero_left _)

theorem row_update_exact {W : Usize} (powers steps : Array Word512 W) :
    let products := List.zipWith productsReduced powers.val steps.val
    (rowUpdate zero powers steps).1.bv = AvxHorizontalXor.parity (reduceTile products) ∧
    (rowUpdate zero powers steps).2.val = products := by
  let state := BulksketchBridge.MutableZip.stateAt powers.to_slice steps.to_slice 0
  have same : powers.to_slice.length = steps.to_slice.length := by
    simp [Array.to_slice, Slice.length]
  have math := power_writes_math powers.to_slice steps.to_slice same 0 (by omega) zero id
  let products := List.zipWith productsReduced powers.val steps.val
  have payload : tailProducts powers.to_slice steps.to_slice 0 = products := by
    simp [tailProducts, Array.to_slice, products]
  have sumMath : (powerWrites powers.to_slice.length state id zero).1 =
      reduceTile products := by
    have exact := math.1
    simp only [Nat.sub_zero, payload, fold_registers_zero] at exact
    exact exact
  have frameMath :
      (powerWrites powers.to_slice.length state id zero).2.2
        (powerWrites powers.to_slice.length state id zero).2.1 =
      finalState powers.to_slice steps.to_slice same 0 (by omega) := by
    have exact := math.2
    simp only [Nat.sub_zero, id] at exact
    exact exact
  have finalWords : (finalState powers.to_slice steps.to_slice same 0 (by omega)).fst.slice.val =
      products := by
    simp only [finalState, Slice.from_val, List.take_zero, List.nil_append, payload]
  have fits : products.length = W.val := by
    simp [products]
  generalize exact : powerWrites powers.to_slice.length state id zero = result
  rcases result with ⟨sum, written, restore⟩
  rw [exact] at sumMath frameMath
  change sum = reduceTile products at sumMath
  change restore written = _ at frameMath
  have exactUpdate : rowUpdate zero powers steps =
      (⟨AvxHorizontalXor.parity sum⟩, powers.from_slice (restore written).fst.slice) := by
    unfold rowUpdate
    change (let (sum, written, restore) := powerWrites powers.to_slice.length state id zero
            ((⟨AvxHorizontalXor.parity sum⟩ : U64), powers.from_slice (restore written).fst.slice)) = _
    rw [exact]
  rw [exactUpdate]
  constructor
  · exact congrArg AvxHorizontalXor.parity sumMath
  · change (powers.from_slice (restore written).fst.slice).val = products
    rw [frameMath, Array.from_slice_val]
    · exact finalWords
    · rw [finalWords]
      exact fits

theorem row_schedule {W : Usize} (bases : List Word512) (row : Nat)
    (powers steps : Array Word512 W)
    (powersExact : powers.val = bases.map (fun base => step base row))
    (stepsExact : steps.val = bases.map (fun base => productsReduced base base)) :
    (rowUpdate zero powers steps).1.bv =
      AvxHorizontalXor.parity (reduceTile (bases.map (fun base => step base (row + 1)))) ∧
    (rowUpdate zero powers steps).2.val = bases.map (fun base => step base (row + 1)) := by
  have exact := row_update_exact powers steps
  rw [powersExact, stepsExact, List.zipWith_map, List.zipWith_self] at exact
  exact exact

theorem first_row_fold (W : Usize) (ids : Slice U64) :
    ((arraysAfterInit W ids).1.val).foldl xorRegister zero =
      reduceTile ((AvxTileChunkSum.tileChunks ids W.val).map AvxSquare.loadWords) := by
  rw [fold_registers_zero, (initialized_arrays W ids).1]

#print axioms row_schedule
#print axioms first_row_fold

end BulksketchBridge.AvxTileRowMath
