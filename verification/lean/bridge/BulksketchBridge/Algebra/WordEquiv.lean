import BulksketchBridge.Algebra.Word
import BulksketchBridge.Algebra.TraceSpec

/-! A complete representation equivalence, using the explicitly proved
polynomial-basis map rather than an arbitrary equivalence of finite types. -/

namespace BulksketchBridge.Algebra.Gf64

private def bitVecFinEquiv : BitVec 64 ≃ Fin (2 ^ 64) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv := BitVec.ofFin_toFin
  right_inv := BitVec.toFin_ofFin

theorem word_natCard : Nat.card (BitVec 64) = 2 ^ 64 := by
  rw [Nat.card_congr bitVecFinEquiv, Nat.card_fin]

/-- Every quotient value has exactly one complete canonical 64-bit word. -/
theorem toField_surjective : Function.Surjective toField := by
  letI : Finite (BitVec 64) :=
    Finite.of_injective BitVec.toFin (fun _ _ => BitVec.eq_of_toFin_eq)
  have sameCard : Nat.card (BitVec 64) = Nat.card Field := by
    rw [word_natCard, field_natCard]
  exact toField_injective.surjective_of_finite (Finite.card_eq.mp sameCard).some

/-- This equivalence's forward map is the actual polynomial interpretation. -/
noncomputable def wordFieldEquiv : BitVec 64 ≃ Field :=
  Equiv.ofBijective toField ⟨toField_injective, toField_surjective⟩

@[simp] theorem wordFieldEquiv_apply (input : BitVec 64) :
    wordFieldEquiv input = toField input := rfl

end BulksketchBridge.Algebra.Gf64
