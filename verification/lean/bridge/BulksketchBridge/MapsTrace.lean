import BulksketchBridge.MapsTraceChallenges

/-!
Exact full-byte refinement of the unchanged actual native trace endpoint.
The conversion is proved inner Ok for every U64 input, so the expect path never
formats an error. Absolute-trace algebra is a separate additive theorem.
-/

namespace BulksketchBridge.MapsTrace

open Aeneas Aeneas.Std

private theorem canonical_mask (word : U64) :
    word &&& ~~~bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK = 0#u64 := by
  apply U64.bv_eq_imp_eq
  simp [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK,
    core.num.U64.MAX, U64.rMax]

private theorem shift_right_61 (word : U64) :
    word >>> (61#i32) = Result.ok (⟨word.bv >>> (61 : Nat)⟩ : U64) := by rfl

private theorem shift_right_63 (word : U64) :
    word >>> (63#i32) = Result.ok (⟨word.bv >>> (63 : Nat)⟩ : U64) := by rfl

/-- The source's masked value is always a bit, independently of the input. -/
theorem selector_bounded (input : U64) :
    ((((⟨input.bv >>> (61 : Nat)⟩ : U64) ^^^
      (⟨input.bv >>> (63 : Nat)⟩ : U64)) &&& 1#u64).val) ≤ 1 := by
  change ((((input.bv >>> (61 : Nat)) ^^^ (input.bv >>> (63 : Nat))) &&&
    (1 : BitVec 64)).toNat) ≤ 1
  rw [BitVec.toNat_and]
  exact Nat.and_le_right

/-- The actual general checked conversion returns inner Ok with every expected
output bit; no Debug implementation is ever invoked by the source expect. -/
theorem selector_conversion_normal (input : U64) :
    U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from
      (((⟨input.bv >>> (61 : Nat)⟩ : U64) ^^^
        (⟨input.bv >>> (63 : Nat)⟩ : U64)) &&& 1#u64) =
          Result.ok (.Ok (expectedWord input)) := by
  have inRange :
      (((⟨input.bv >>> (61 : Nat)⟩ : U64) ^^^
        (⟨input.bv >>> (63 : Nat)⟩ : U64)) &&& 1#u64).val ≤ UScalar.max .U8 := by
    exact Nat.le_trans (selector_bounded input)
      (by simp [U8.max_eq])
  simp only [U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from,
    core.num.tryFromUScalar, inRange, ite_true]
  rfl

/-- Every original native Gf64 trace call returns the complete frozen selector byte. -/
theorem trace_refines :
    BulksketchBridge.MapsTraceChallenges.normalResultMatchesSelector := by
  intro input
  simp only [bulksketch.field.maps.trace,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS,
    lift, bind_ok, canonical_mask, ite_true, shift_right_61, shift_right_63,
    selector_conversion_normal, core.result.Result.expect]

end BulksketchBridge.MapsTrace
