import BulksketchBridge.AvxEncode18Stores

namespace BulksketchBridge.AvxEncode18

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime Aeneas.Std.AvxEncode18Runtime
open X86MaskedMemory AvxSquare Algebra.Gf64 DenseCoefficient RebuiltLfsr
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 700000

attribute [local irreducible] rowPayload storeWords

theorem row_payload_word (odd : Slice U64) (values : Triple) (room : 18 ≤ odd.length) (i : Fin 18) :
    (rowPayload odd values room)[i.val]!.bv = rowLane values i := by
  obtain ⟨_, lowWidth, _, highWidth, tailWidth⟩ := windows_length odd room
  let low := storeWords (lowWindow odd) values.1 (by rw [lowWidth])
  let high := storeWords (highWindow odd) values.2.1 (by rw [highWidth])
  let tail := storeWords (tailWindow odd) values.2.2 (by rw [tailWidth]; decide)
  have lowLen : low.val.length = 8 := (store_length ..).trans lowWidth
  have highLen : high.val.length = 8 := (store_length ..).trans highWidth
  unfold rowPayload
  change (low.val ++ high.val ++ tail.val)[i.val]!.bv = _
  rw [List.append_assoc]
  by_cases early : i.val < 8
  · rw [List.getElem!_append_left low.val (high.val ++ tail.val) i.val (by omega)]
    rw [rowLane, dite_eq_left early]
    have stored := store_word (lowWindow odd) values.1 (by rw [lowWidth]) i.val (by omega)
    rw [Slice.getElem!_Nat_eq] at stored
    exact stored
  · rw [List.getElem!_append_right _ _ _ (by omega), lowLen, rowLane, dite_eq_right early]
    by_cases middle : i.val < 16
    · rw [List.getElem!_append_left high.val tail.val (i.val - 8) (by omega)]
      rw [dite_eq_left middle]
      have stored := store_word (highWindow odd) values.2.1 (by rw [highWidth]) (i.val - 8) (by omega)
      rw [Slice.getElem!_Nat_eq] at stored
      exact stored
    · rw [List.getElem!_append_right high.val tail.val (i.val - 8) (by omega),
        highLen, dite_eq_right middle, show i.val - 8 - 8 = i.val - 16 by omega]
      have stored := store_word (tailWindow odd) values.2.2 (by rw [tailWidth]; decide)
        (i.val - 16) (by have := i.isLt; omega)
      rw [Slice.getElem!_Nat_eq] at stored
      exact stored

noncomputable def encodeValue (ids : Slice U64) (i : Nat) : Field :=
  if ids.length = 2 then toField ids[0]!.bv ^ (2 * i + 1) + toField ids[1]!.bv ^ (2 * i + 1)
  else toField ids[0]!.bv ^ (2 * i + 1)

/-- Original fast encoder for the admitted one- or two-ID case. -/
def ActualEncode18 : Prop :=
  ∀ (baseModel : Bases) (storeModel : Store), BasesLaw baseModel → StoreLaw storeModel →
    ∀ (odd ids : Slice U64), 18 ≤ odd.length → (ids.length = 1 ∨ ids.length = 2) →
      ∃ output,
        encode_18 baseModel storeModel odd ids = .ok output ∧ output.length = odd.length ∧
        (∀ i : Fin 18, toField output[i.val]!.bv = encodeValue ids i.val) ∧
        (∀ i : Nat, 18 ≤ i → output[i]! = odd[i]!)

theorem encode_refines : ActualEncode18 := by
  intro baseModel storeModel basis storeLaw odd ids room admitted
  obtain ⟨values, ran, field⟩ := encode_words baseModel basis storeModel storeLaw odd ids room admitted
  let output := odd.setSlice! 0 (rowPayload odd values room)
  have size := row_payload_length odd values room
  refine ⟨output, ran, Slice.setSlice!_length .., ?_, ?_⟩
  · intro i
    have bound := i.isLt
    have read : output[i.val]! = (rowPayload odd values room)[i.val]! := by
      have within : 0 ≤ i.val ∧ i.val - 0 < (rowPayload odd values room).length ∧ i.val < odd.length := by
        rw [size]
        omega
      have exactRead := Slice.setSlice!_getElem!_middle odd (rowPayload odd values room) 0 i.val within
      rw [Nat.sub_zero] at exactRead
      exact exactRead
    calc
      _ = toField (rowPayload odd values room)[i.val]!.bv := congrArg (fun word : U64 => toField word.bv) read
      _ = toField (rowLane values i) := congrArg toField (row_payload_word odd values room i)
      _ = _ := field i
  · intro i outside
    apply Slice.setSlice!_getElem!_suffix
    rw [Nat.zero_add, size]
    exact outside

end BulksketchBridge.AvxEncode18
