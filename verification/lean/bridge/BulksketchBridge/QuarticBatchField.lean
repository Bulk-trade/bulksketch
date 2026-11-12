import BulksketchBridge.QuarticLoop
import Mathlib.Tactic.FieldSimp

namespace BulksketchBridge.QuarticLoops

open Aeneas.Std Algebra.Gf64

private theorem mul_field (left right : U64) : toField (mulWord left right).bv =
    toField left.bv * toField right.bv := toField_mul _ _

private theorem xor_field (left right : U64) : toField (left ^^^ right).bv =
    toField left.bv + toField right.bv := toField_xor _ _

/-- The initial inverse callback is applied to the product of all four roots. -/
theorem total_product_field (roots : Words) :
    toField (mulWord (prefixes roots)[3]! roots[3]!).bv =
      toField roots[0]!.bv * toField roots[1]!.bv * toField roots[2]!.bv * toField roots[3]!.bv := by
  simp only [mul_field, prefixes, Array.getElem!_Nat_eq, Array.make, Array.from_val,
    List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem total_product_nonzero (roots : Words)
    (nonzero : ∀ i : Fin 4, toField roots[i.val]!.bv ≠ 0) :
    toField (mulWord (prefixes roots)[3]! roots[3]!).bv ≠ 0 := by
  rw [total_product_field]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (nonzero 0) (nonzero 1)) (nonzero 2)) (nonzero 3)

private theorem batch_field {K : Type} [_root_.Field K] (a b c d shift : K)
    (first : a ≠ 0) (second : b ≠ 0) (third : c ≠ 0) (fourth : d ≠ 0) :
    let inv := (a * b * c * d)⁻¹
    inv * d * c * b + shift = a⁻¹ + shift ∧
    a * (inv * d * c) + shift = b⁻¹ + shift ∧
    (a * b) * (inv * d) + shift = c⁻¹ + shift ∧
    (a * b * c) * inv + shift = d⁻¹ + shift := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp

set_option maxHeartbeats 2000000 in
/-- The exact reverse frame sends each original nonzero root to its inverse plus the shift. -/
theorem shiftedReciprocals_field (roots : Words) (shift inverse : U64)
    (nonzero : ∀ i : Fin 4, toField roots[i.val]!.bv ≠ 0)
    (inv : toField inverse.bv = (toField (mulWord (prefixes roots)[3]! roots[3]!).bv)⁻¹)
    (index : Fin 4) :
    toField (shiftedReciprocals roots (prefixes roots) shift inverse)[index.val]!.bv =
      (toField roots[index.val]!.bv)⁻¹ + toField shift.bv := by
  have nz (i : Nat) (bound : i < 4) : toField roots.val[i]!.bv ≠ 0 := by
    simpa only [Array.getElem!_Nat_eq] using (nonzero ⟨i, bound⟩)
  have first := nz 0 (by decide)
  have second := nz 1 (by decide)
  have third := nz 2 (by decide)
  have fourth := nz 3 (by decide)
  have one : toField (1#u64).bv = 1 := toField_one
  rw [total_product_field] at inv
  simp only [Array.getElem!_Nat_eq] at inv
  obtain ⟨zero, oneSlot, twoSlot, threeSlot⟩ :=
    batch_field (toField roots.val[0]!.bv) (toField roots.val[1]!.bv)
      (toField roots.val[2]!.bv) (toField roots.val[3]!.bv) (toField shift.bv) first second third fourth
  fin_cases index <;>
    simp only [shiftedReciprocals, prefixes, Array.getElem!_Nat_eq, Array.make, Array.from_val,
      List.getElem!_cons_succ, List.getElem!_cons_zero, mul_field, xor_field, one, one_mul] <;>
    rw [inv]
  · exact zero
  · exact oneSlot
  · exact twoSlot
  · exact threeSlot

/-- The complete native reverse frame has the input ordering and multiplicities. -/
theorem shiftedReciprocals_field_list (roots : Words) (shift inverse : U64)
    (nonzero : ∀ i : Fin 4, toField roots[i.val]!.bv ≠ 0)
    (inv : toField inverse.bv = (toField (mulWord (prefixes roots)[3]! roots[3]!).bv)⁻¹) :
    (shiftedReciprocals roots (prefixes roots) shift inverse).val.map (fun word => toField word.bv) =
      roots.val.map (fun word => (toField word.bv)⁻¹ + toField shift.bv) := by
  apply List.ext_getElem (by simp)
  intro index leftBound rightBound
  have valid : index < 4 := by simpa using rightBound
  have outputBound : index < (shiftedReciprocals roots (prefixes roots) shift inverse).val.length := by
    simpa only [List.length_map] using leftBound
  have inputBound : index < roots.val.length := by simpa only [List.length_map] using rightBound
  simp only [List.getElem_map]
  rw [List.Inhabited_getElem_eq_getElem! _ _ outputBound,
    List.Inhabited_getElem_eq_getElem! _ _ inputBound]
  have point := shiftedReciprocals_field roots shift inverse nonzero inv (⟨index, valid⟩ : Fin 4)
  simpa only [Array.getElem!_Nat_eq] using point

end BulksketchBridge.QuarticLoops
