import Arithmetic.AvxInsert18Generated
import BulksketchBridge.AvxInsertionBasesStatic

namespace BulksketchBridge.AvxInsert18

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime Aeneas.Std.AvxEncode18Runtime
open X86MaskedMemory AvxSquare AvxEncode18 Algebra.Gf64 DenseCoefficient RebuiltLfsr
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

def inputRegisters (odd : Slice U64) : Triple :=
  (loadWords (lowWindow odd), loadWords (highWindow odd), loadWords (tailWindow odd))

theorem insert_words (baseModel : Bases) (basis : BasesLaw baseModel)
    (loadModel : Load) (loadLaw : LoadLaw loadModel) (storeModel : Store) (storeLaw : StoreLaw storeModel)
    (odd : Slice U64) (id : U64) (room : 18 ≤ odd.length) :
    ∃ values,
      insert_18 baseModel loadModel storeModel odd id =
        .ok (odd.setSlice! 0 (rowPayload odd (xorTriple (inputRegisters odd) values) room)) ∧
      ∀ i : Fin 18, toField (rowLane values i) = toField id.bv ^ (2 * i.val + 1) := by
  obtain ⟨values, powers, meaning⟩ := powers_refines baseModel basis id
  refine ⟨values, ?_, meaning⟩
  trans store18 storeModel odd (xorTriple (inputRegisters odd) values)
  · obtain ⟨prefixWidth, lowWidth, restWidth, highWidth, tailWidth⟩ := windows_length odd room
    have width18 : (18#usize).val = 18 := by simp
    have width8 : (8#usize).val = 8 := by simp
    have front := prefix_normal odd 18#usize (by rwa [width18])
    have split0 := BmEntry.split_refines (prefix18 odd) 8#usize (by rw [width8, prefixWidth]; decide)
    have split1 := BmEntry.split_refines (restWindow odd) 8#usize (by rw [width8, restWidth]; decide)
    have exactPrefix : prefixSlice odd (18#usize).val = prefix18 odd := by rw [width18]; rfl
    have exactRest : BmEntry.tail (prefix18 odd) 8 = restWindow odd := rfl
    have exactLow : prefixSlice (prefix18 odd) 8 = lowWindow odd := rfl
    have exactHigh : prefixSlice (restWindow odd) 8 = highWindow odd := rfl
    have exactTail : BmEntry.tail (restWindow odd) 8 = tailWindow odd := rfl
    simp only [insert_18, powers, store18, bind_ok]
    dsimp! only
    simp only [Slice.index_mut_SliceIndexRangeToUsizeSliceInst, front, exactPrefix, bind_ok]
    dsimp! only
    simp only [split0, width8, exactRest, bind_ok]
    dsimp! only
    simp only [split1, width8, exactLow, exactHigh, exactTail, bind_ok]
    dsimp! only
    simp only [loadLaw (lowWindow odd) (by omega), loadLaw (highWindow odd) (by omega),
      loadLaw (tailWindow odd) (by omega), xorWords, bind_ok, xorTriple, inputRegisters]
    rfl
  · exact store18_refines storeModel storeLaw odd _ room

theorem low_region (odd : Slice U64) : lowWindow odd = ClosedLeaf.region odd 0 8 := by
  apply Slice.ext
  simp [lowWindow, prefix18, prefixSlice, ClosedLeaf.region, List.slice, List.take_take]

theorem high_region (odd : Slice U64) : highWindow odd = ClosedLeaf.region odd 8 16 := by
  apply Slice.ext
  simp [highWindow, restWindow, prefix18, prefixSlice, BmEntry.tail, ClosedLeaf.region,
    List.slice, List.drop_take, List.take_take]

theorem tail_region (odd : Slice U64) : tailWindow odd = ClosedLeaf.region odd 16 18 := by
  apply Slice.ext
  simp [tailWindow, restWindow, prefix18, prefixSlice, BmEntry.tail, ClosedLeaf.region,
    List.slice, List.drop_take, List.drop_drop]

private theorem region_lane (words : Slice U64) (start stop : Nat)
    (lane : Fin 8) (room : stop ≤ words.length) (active : start + lane.val < stop) :
    flatten (loadWords (ClosedLeaf.region words start stop)) lane = words[start + lane.val]!.bv := by
  let region := ClosedLeaf.region words start stop
  have length : region.length = stop - start := ClosedLeaf.region_length _ _ _ room
  have exactLoad : loadWords region =
      unflatten (fun i => if i.val < region.length then region[i.val]!.bv else 0) := rfl
  rw [show ClosedLeaf.region words start stop = region from rfl, exactLoad, flatten_unflatten,
    ite_eq_left (by omega : lane.val < region.length)]
  have payload : region[lane.val]! = words[start + lane.val]! := by
    simp only [region, ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
    exact List.getElem!_slice start stop lane.val words.val ⟨room, active⟩
  rw [payload]

theorem input_register_word (odd : Slice U64) (i : Fin 18) (room : 18 ≤ odd.length) :
    rowLane (inputRegisters odd) i = odd[i.val]!.bv := by
  unfold rowLane inputRegisters
  by_cases low : i.val < 8
  · rw [dite_eq_left low, low_region]
    simpa only [Nat.zero_add] using region_lane odd 0 8 ⟨i.val, low⟩ (by omega) (by simpa using low)
  · rw [dite_eq_right low]
    by_cases high : i.val < 16
    · rw [dite_eq_left high, high_region]
      have read := region_lane odd 8 16 ⟨i.val - 8, by omega⟩ (by omega)
        (by change 8 + (i.val - 8) < 16; omega)
      simpa only [show 8 + (i.val - 8) = i.val by omega] using read
    · rw [dite_eq_right high, tail_region]
      have bound := i.isLt
      have read := region_lane odd 16 18 ⟨i.val - 16, by omega⟩ (by omega)
        (by change 16 + (i.val - 16) < 18; omega)
      simpa only [show 16 + (i.val - 16) = i.val by omega] using read

theorem row_xor (left right : Triple) (i : Fin 18) :
    rowLane (xorTriple left right) i = rowLane left i ^^^ rowLane right i := by
  unfold rowLane xorTriple
  split <;> try rfl
  split <;> rfl

def ActualInsert18 : Prop :=
  ∀ (baseModel : Bases) (loadModel : Load) (storeModel : Store),
    BasesLaw baseModel → LoadLaw loadModel → StoreLaw storeModel →
    ∀ (odd : Slice U64) (id : U64), 18 ≤ odd.length →
      ∃ output, insert_18 baseModel loadModel storeModel odd id = .ok output ∧ output.length = odd.length ∧
        (∀ i : Fin 18, toField output[i.val]!.bv = toField odd[i.val]!.bv + toField id.bv ^ (2 * i.val + 1)) ∧
        (∀ i : Nat, 18 ≤ i → output[i]! = odd[i]!)

attribute [local irreducible] rowPayload

theorem insert_refines : ActualInsert18 := by
  intro baseModel loadModel storeModel basis loadLaw storeLaw odd id room
  obtain ⟨values, ran, powers⟩ := insert_words baseModel basis loadModel loadLaw storeModel storeLaw odd id room
  let update := xorTriple (inputRegisters odd) values
  let payload := rowPayload odd update room
  let output := odd.setSlice! 0 payload
  have length : payload.length = 18 := row_payload_length odd update room
  refine ⟨output, ran, Slice.setSlice!_length .., ?_, ?_⟩
  · intro i
    have bounded := i.isLt
    have read := Slice.setSlice!_getElem!_middle odd payload 0 i.val (by rw [length]; omega)
    rw [Nat.sub_zero] at read
    calc
      _ = toField payload[i.val]!.bv := congrArg (fun word : U64 => toField word.bv) read
      _ = toField (rowLane update i) := congrArg toField (row_payload_word odd update room i)
      _ = _ := by simp only [update, row_xor, toField_xor, input_register_word odd i room, powers i]
  · intro i after
    apply Slice.setSlice!_getElem!_suffix
    rw [Nat.zero_add, length]
    exact after

theorem static_insert_refines (loadModel : Load) (storeModel : Store)
    (loadLaw : LoadLaw loadModel) (storeLaw : StoreLaw storeModel)
    (odd : Slice U64) (id : U64) (room : 18 ≤ odd.length) :
    ∃ output,
      insert_18 (single_bases INSERT_BASES loadModel) loadModel storeModel odd id = .ok output ∧
      output.length = odd.length ∧
      (∀ i : Fin 18, toField output[i.val]!.bv = toField odd[i.val]!.bv + toField id.bv ^ (2 * i.val + 1)) ∧
      (∀ i : Nat, 18 ≤ i → output[i]! = odd[i]!) :=
  insert_refines _ loadModel storeModel (AvxInsertionBases.static_supplies_bases loadModel loadLaw)
    loadLaw storeLaw odd id room

end BulksketchBridge.AvxInsert18
