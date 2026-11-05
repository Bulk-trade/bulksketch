import BulksketchBridge.MapsTrace
import BulksketchBridge.MapsTraceMathChallenges
import BulksketchProofs.Field.Maps

namespace BulksketchBridge.MapsTraceMath

open Aeneas Aeneas.Std BulksketchProofs.Field

private theorem selected_bit (input : BitVec 64) :
    ((input >>> 61) ^^^ (input >>> 63)).getLsbD 0 = Maps.traceBit input := by
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, Maps.traceBit]

private theorem selected_byte_bits (input : BitVec 64) :
    MapsTrace.expectedBits input = if Maps.traceBit input then 1 else 0 := by
  have maskEq := BitVec.and_one_eq_setWidth_ofBool_getLsbD
    (x := ((input >>> 61) ^^^ (input >>> 63)))
  have lifted := congrArg (fun bits : BitVec 64 => bits.setWidth 8) maskEq
  calc
    MapsTrace.expectedBits input =
        (BitVec.setWidth 64 (BitVec.ofBool (((input >>> 61) ^^^ (input >>> 63)).getLsbD 0))).setWidth 8 := lifted
    _ = if Maps.traceBit input then 1 else 0 := by
      rw [selected_bit]
      cases bitCase : Maps.traceBit input <;> simp

/-- Zero-extending the complete native selector byte gives exactly the pure trace word. -/
theorem selector_matches_trace_word (input : U64) :
    (MapsTrace.expectedWord input).bv.setWidth 64 = Maps.traceWord input.bv := by
  change (MapsTrace.expectedBits input.bv).setWidth 64 = _
  rw [selected_byte_bits]
  cases bitCase : Maps.traceBit input.bv <;> simp [Maps.traceWord, bitCase]

/-- The source byte is exactly zero or one according to the independent selector. -/
theorem trace_byte_case (input : U64) :
    MapsTrace.expectedWord input =
      if Maps.traceBit input.bv then 1#u8 else 0#u8 := by
  apply U8.bv_eq_imp_eq
  cases bitCase : Maps.traceBit input.bv <;>
    simp only [MapsTrace.expectedWord, selected_byte_bits, bitCase, Bool.false_eq_true,
      ite_true, ite_false, U8.ofNat_bv]
  all_goals rfl

/-- No upper byte bit can be set by the native selector. -/
theorem selector_value_bounded (input : U64) : (MapsTrace.expectedWord input).val ≤ 1 := by
  change (MapsTrace.expectedBits input.bv).toNat ≤ 1
  unfold MapsTrace.expectedBits
  rw [BitVec.toNat_setWidth]
  exact Nat.le_trans (Nat.mod_le _ _) (MapsTrace.selector_bounded input)

/-- Actual native full-byte output equals the independent64-conjugate absolute trace. -/
theorem trace_matches_absolute : MapsTraceMathChallenges.actualTraceMatchesAbsoluteTrace := by
  intro input
  refine ⟨MapsTrace.expectedWord input, MapsTrace.trace_refines input, ?_, selector_value_bounded input⟩
  rw [selector_matches_trace_word]
  exact (Maps.absoluteTrace_eq_selector input.bv).symm

end BulksketchBridge.MapsTraceMath
