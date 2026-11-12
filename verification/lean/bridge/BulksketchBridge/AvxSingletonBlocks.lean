import BulksketchBridge.AvxUpdateSingleBlock
import BulksketchBridge.AvxEncode18Stores

namespace BulksketchBridge.AvxSingleton

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register
open AvxSquare AvxUpdateSingleBlock X86MaskedMemory DenseCoefficient RebuiltLfsr

set_option maxHeartbeats 1400000

@[simp] theorem block_length (odd : Slice U64) (offset : Nat) (value : Word512) :
    (blockOutput odd offset value).length = odd.length := by
  unfold blockOutput
  dsimp only
  split <;> simp only [Slice.setSlice!_length]

private theorem load_lane (odd : Slice U64) (start stop : Nat) (lane : Fin 8)
    (room : stop ≤ odd.length) (active : start + lane.val < stop) :
    flatten (loadWords (ClosedLeaf.region odd start stop)) lane = odd[start + lane.val]!.bv := by
  let region := ClosedLeaf.region odd start stop
  have length : region.length = stop - start := ClosedLeaf.region_length _ _ _ room
  have exactLoad : loadWords region =
      unflatten (fun i => if i.val < region.length then region[i.val]!.bv else 0) := rfl
  rw [show ClosedLeaf.region odd start stop = region from rfl, exactLoad, flatten_unflatten,
    ite_eq_left (by omega : lane.val < region.length)]
  have payload : region[lane.val]! = odd[start + lane.val]! := by
    simp only [region, ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
    exact List.getElem!_slice start stop lane.val odd.val ⟨room, active⟩
  rw [payload]

theorem block_word (odd : Slice U64) (start row : Nat) (value : Word512)
    (inside : row < odd.length) :
    (blockOutput odd start value)[row]!.bv =
      if here : start ≤ row ∧ row < start + 8
      then odd[row]!.bv ^^^ flatten value ⟨row - start, by omega⟩
      else odd[row]!.bv := by
  let stop := blockStop odd start
  let region := ClosedLeaf.region odd start stop
  have room : stop ≤ odd.length := Nat.min_le_right _ _
  have length : region.length = stop - start := ClosedLeaf.region_length _ _ _ room
  have stopEq : stop = min (start + 8) odd.length := rfl
  have fits : region.length ≤ 8 := by omega
  let written := storeWords region (blockRegister odd start value) fits
  have width : written.length = stop - start := (AvxEncode18.store_length ..).trans length
  unfold blockOutput
  dsimp only
  change (if h : region.length ≤ 8 then odd.setSlice! start
      (storeWords region (blockRegister odd start value) h).val else odd)[row]!.bv = _
  rw [dite_eq_left fits]
  change (odd.setSlice! start written.val)[row]!.bv = _
  by_cases here : start ≤ row ∧ row < start + 8
  · rw [dite_eq_left here,
      Slice.setSlice!_getElem!_middle _ _ _ _ (by change start ≤ row ∧ row - start < written.length ∧ _; omega),
      ← Slice.getElem!_Nat_eq]
    rw [AvxEncode18.store_word region _ fits (row - start) (by omega)]
    have lane := load_lane odd start stop ⟨row - start, by omega⟩ room (by dsimp only; omega)
    have exactRow : start + (row - start) = row := by omega
    rw [show (flatten (blockRegister odd start value) ⟨row - start, by omega⟩) =
        flatten (loadWords region) ⟨row - start, by omega⟩ ^^^ flatten value ⟨row - start, by omega⟩ from rfl,
      lane, exactRow]
  · rw [dite_eq_right here]
    by_cases before : row < start
    · rw [Slice.setSlice!_getElem!_prefix _ _ _ _ before]
    · rw [Slice.setSlice!_getElem!_suffix _ _ _ _ (by change start + written.length ≤ row; omega)]

def writeBlocks : List Word512 → Slice U64 → Nat → Slice U64
  | [], odd, _ => odd
  | value :: rest, odd, start => writeBlocks rest (blockOutput odd start value) (start + 8)

@[simp] theorem blocks_length (values : List Word512) (odd : Slice U64) (start : Nat) :
    (writeBlocks values odd start).length = odd.length := by
  induction values generalizing odd start with
  | nil => rfl
  | cons value rest ih => simp [writeBlocks, ih]

theorem blocks_word (values : List Word512) (odd : Slice U64) (start row : Nat)
    (inside : row < odd.length) :
    (writeBlocks values odd start)[row]!.bv =
      if _here : start ≤ row ∧ row < start + 8 * values.length then
        odd[row]!.bv ^^^ flatten values[(row - start) / 8]! ⟨(row - start) % 8, Nat.mod_lt _ (by decide)⟩
      else odd[row]!.bv := by
  induction values generalizing odd start with
  | nil => simp [writeBlocks]
  | cons value rest ih =>
    rw [writeBlocks, ih _ (start + 8) (by simpa using inside), block_word odd start row value inside]
    simp only [List.length_cons]
    by_cases before : row < start
    · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]
    · by_cases head : row < start + 8
      · rw [dite_eq_right (by omega), dite_eq_left (by omega), dite_eq_left (by omega)]
        have block : (row - start) / 8 = 0 := by omega
        have lane : (row - start) % 8 = row - start := by omega
        rw [block, List.getElem!_cons_zero]
        congr 1
        exact congrArg (flatten value) (Fin.ext lane.symm)
      · by_cases tail : row < start + 8 * (rest.length + 1)
        · rw [dite_eq_left (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
          have block : (row - start) / 8 = (row - (start + 8)) / 8 + 1 := by omega
          have lane : (row - start) % 8 = (row - (start + 8)) % 8 := by omega
          rw [block, List.getElem!_cons_succ]
          congr 1
          exact congrArg (flatten rest[(row - (start + 8)) / 8]!) (Fin.ext lane.symm)
        · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]

end BulksketchBridge.AvxSingleton
