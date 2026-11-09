import BulksketchBridge.AvxEncode18Powers
import BulksketchBridge.AvxSquareScalarMemory
import BulksketchBridge.BmEntry

namespace BulksketchBridge.AvxEncode18

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime Aeneas.Std.AvxEncode18Runtime
open X86MaskedMemory AvxSquare Algebra.Gf64 DenseCoefficient RebuiltLfsr
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

def xorTriple (a b : Triple) : Triple :=
  (xorRegister a.1 b.1, xorRegister a.2.1 b.2.1, xorRegister a.2.2 b.2.2)

def prefix18 (words : Slice U64) : Slice U64 := prefixSlice words 18
def lowWindow (words : Slice U64) : Slice U64 := prefixSlice (prefix18 words) 8
def restWindow (words : Slice U64) : Slice U64 := BmEntry.tail (prefix18 words) 8
def highWindow (words : Slice U64) : Slice U64 := prefixSlice (restWindow words) 8
def tailWindow (words : Slice U64) : Slice U64 := BmEntry.tail (restWindow words) 8

theorem windows_length (words : Slice U64) (room : 18 ≤ words.length) :
    (prefix18 words).length = 18 ∧ (lowWindow words).length = 8 ∧ (restWindow words).length = 10 ∧
      (highWindow words).length = 8 ∧ (tailWindow words).length = 2 := by
  have first : (prefix18 words).length = 18 := by simp only [prefix18, prefix_length, Nat.min_eq_left room]
  simp [first, lowWindow, highWindow, tailWindow, restWindow]

theorem store_length (words : Slice U64) (value : Word512) (bound : words.length ≤ 8) :
    (storeWords words value bound).length = words.length := by
  simp [storeWords, registerPayload, Slice.length]

def rowPayload (words : Slice U64) (values : Triple) (room : 18 ≤ words.length) : List U64 :=
  let widths := windows_length words room
  (storeWords (lowWindow words) values.1 (by rw [widths.2.1])).val ++
  (storeWords (highWindow words) values.2.1 (by rw [widths.2.2.2.1])).val ++
  (storeWords (tailWindow words) values.2.2 (by rw [widths.2.2.2.2]; decide)).val

theorem row_payload_length (words : Slice U64) (values : Triple) (room : 18 ≤ words.length) :
    (rowPayload words values room).length = 18 := by
  have widths := windows_length words room
  unfold rowPayload
  simp only [List.length_append]
  change (storeWords (lowWindow words) values.1 _).length +
    (storeWords (highWindow words) values.2.1 _).length +
    (storeWords (tailWindow words) values.2.2 _).length = 18
  rw [store_length, store_length, store_length, widths.2.1, widths.2.2.2.1, widths.2.2.2.2]

def store18 (storeModel : Store) (odd : Slice U64) (values : Triple) : Result (Slice U64) := do
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice U64) odd ⟨18#usize⟩
  let ((low_words, rest), split_at_mut_back) ← core.slice.Slice.split_at_mut s 8#usize
  let ((high_words, tail_words), split_at_mut_back1) ← core.slice.Slice.split_at_mut rest 8#usize
  let low_words1 ← storeModel low_words values.1
  let high_words1 ← storeModel high_words values.2.1
  let tail_words1 ← storeModel tail_words values.2.2
  let rest1 := split_at_mut_back1 (high_words1, tail_words1)
  let s1 := split_at_mut_back (low_words1, rest1)
  .ok (index_mut_back s1)

theorem store18_refines (storeModel : Store) (storeLaw : StoreLaw storeModel)
    (odd : Slice U64) (values : Triple) (room : 18 ≤ odd.length) :
    store18 storeModel odd values = .ok (odd.setSlice! 0 (rowPayload odd values room)) := by
  obtain ⟨prefixWidth, lowWidth, restWidth, highWidth, tailWidth⟩ := windows_length odd room
  have width18 : (18#usize).val = 18 := by simp
  have width8 : (8#usize).val = 8 := by simp
  have front := prefix_normal odd 18#usize (by rwa [width18])
  have split0 := BmEntry.split_refines (prefix18 odd) 8#usize (by rw [width8, prefixWidth]; decide)
  have split1 := BmEntry.split_refines (restWindow odd) 8#usize (by rw [width8, restWidth]; decide)
  let low := storeWords (lowWindow odd) values.1 (by rw [lowWidth])
  let high := storeWords (highWindow odd) values.2.1 (by rw [highWidth])
  let tail := storeWords (tailWindow odd) values.2.2 (by rw [tailWidth]; decide)
  have lowLen : low.length = 8 := (store_length ..).trans lowWidth
  have highLen : high.length = 8 := (store_length ..).trans highWidth
  have tailLen : tail.length = 2 := (store_length ..).trans tailWidth
  have lowStore : storeModel (lowWindow odd) values.1 = .ok low := storeLaw _ _ _
  have highStore : storeModel (highWindow odd) values.2.1 = .ok high := storeLaw _ _ _
  have tailStore : storeModel (tailWindow odd) values.2.2 = .ok tail := storeLaw _ _ _
  let combined := BmEntry.splitBack (restWindow odd) 8 (high, tail)
  have combinedVal : combined.val = high.val ++ tail.val := by
    have fits : high.length = min 8 (restWindow odd).length ∧ tail.length = (restWindow odd).length - 8 := by
      rw [highLen, tailLen, restWidth]
      decide
    simp only [combined, BmEntry.splitBack, dite_eq_left fits, Slice.from_val]
  have combinedLen : combined.length = 10 := by
    change combined.val.length = 10
    rw [combinedVal, List.length_append]
    change high.length + tail.length = 10
    omega
  let joined := BmEntry.splitBack (prefix18 odd) 8 (low, combined)
  have joinedVal : joined.val = rowPayload odd values room := by
    have fits : low.length = min 8 (prefix18 odd).length ∧ combined.length = (prefix18 odd).length - 8 := by
      rw [lowLen, combinedLen, prefixWidth]
      decide
    simp only [joined, BmEntry.splitBack, dite_eq_left fits, Slice.from_val, combinedVal,
      rowPayload, low, high, tail, List.append_assoc]
  simp only [store18, Slice.index_mut_SliceIndexRangeToUsizeSliceInst, front, bind_ok]
  dsimp! only
  have exactPrefix : prefixSlice odd (18#usize).val = prefix18 odd := by rw [width18]; rfl
  simp only [exactPrefix, split0, bind_ok, width8]
  dsimp! only
  have exactRest : BmEntry.tail (prefix18 odd) 8 = restWindow odd := rfl
  rw [exactRest]
  simp only [split1, bind_ok, width8]
  dsimp! only
  have exactLow : prefixSlice (prefix18 odd) 8 = lowWindow odd := rfl
  have exactHigh : prefixSlice (restWindow odd) 8 = highWindow odd := rfl
  have exactTail : BmEntry.tail (restWindow odd) 8 = tailWindow odd := rfl
  simp only [exactLow, exactHigh, exactTail, lowStore, highStore, tailStore, bind_ok]
  change Result.ok (restorePrefix odd joined) = _
  simp only [restorePrefix, joinedVal, Slice.setSlice!]

private theorem read_word (words : Slice U64) (i : Usize) (bound : i.val < words.length) :
    Slice.index_usize words i = .ok words[i.val]! := by
  obtain ⟨word, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words i bound)
  rw [normal, value, Slice.getElem!_Nat_eq, List.Inhabited_getElem_eq_getElem! _ _ bound]

/-- Exact native store schedule, including the two-ID XOR and untouched
suffix. The field meaning of the selected lanes is proved below. -/
theorem encode_words (baseModel : Bases) (basis : BasesLaw baseModel)
    (storeModel : Store) (storeLaw : StoreLaw storeModel) (odd ids : Slice U64)
    (room : 18 ≤ odd.length) (admitted : ids.length = 1 ∨ ids.length = 2) :
    ∃ values : Triple,
      encode_18 baseModel storeModel odd ids = .ok (odd.setSlice! 0 (rowPayload odd values room)) ∧
      ∀ i : Fin 18, toField (rowLane values i) =
        if ids.length = 2 then toField ids[0]!.bv ^ (2 * i.val + 1) + toField ids[1]!.bv ^ (2 * i.val + 1)
        else toField ids[0]!.bv ^ (2 * i.val + 1) := by
  obtain ⟨first, firstNormal, firstPower⟩ := powers_refines baseModel basis ids[0]!
  have read0 := read_word ids 0#usize (by change 0 < ids.length; omega)
  have zero : (0#usize).val = 0 := by simp
  rw [zero] at read0
  by_cases two : ids.length = 2
  · obtain ⟨second, secondNormal, secondPower⟩ := powers_refines baseModel basis ids[1]!
    have read1 := read_word ids 1#usize (by change 1 < ids.length; omega)
    have one : (1#usize).val = 1 := by simp
    rw [one] at read1
    have test : Slice.len ids = 2#usize := UScalar.eq_of_val_eq (by rw [Slice.len_val, two]; rfl)
    refine ⟨xorTriple first second, ?_, ?_⟩
    · simp only [encode_18, read0, firstNormal, bind_ok]
      dsimp! only
      simp only [test, ite_true, read1, secondNormal, bind_ok]
      dsimp! only
      simp only [xorWords, bind_ok]
      dsimp! only
      exact store18_refines storeModel storeLaw odd (xorTriple first second) room
    · intro i
      have lane : rowLane (xorTriple first second) i = rowLane first i ^^^ rowLane second i := by
        unfold rowLane xorTriple
        split <;> try rfl
        split <;> rfl
      simp only [two, ite_true, lane, toField_xor, firstPower, secondPower]
  · have test : Slice.len ids ≠ 2#usize := by
      intro eq
      apply two
      simpa [Slice.len_val] using congrArg UScalar.val eq
    refine ⟨first, ?_, ?_⟩
    · simp only [encode_18, read0, firstNormal, bind_ok]
      dsimp! only
      simp only [test, ite_false, bind_ok]
      dsimp! only
      exact store18_refines storeModel storeLaw odd first room
    · intro i
      simp only [two, ite_false, firstPower]

theorem store_word (words : Slice U64) (value : Word512) (bound : words.length ≤ 8)
    (slot : Nat) (active : slot < words.length) :
    (storeWords words value bound)[slot]!.bv = flatten value ⟨slot, by omega⟩ := by
  have length := store_length words value bound
  rw [← Slice.Inhabited_getElem_eq_getElem! _ _ (by omega : slot < (storeWords words value bound).length)]
  rw [Slice.getElem_Nat_eq]
  simp only [storeWords, registerPayload, Slice.from_val, List.getElem_map, List.getElem_ofFn]
  change slot < (storeWords words value bound).length
  omega

end BulksketchBridge.AvxEncode18
