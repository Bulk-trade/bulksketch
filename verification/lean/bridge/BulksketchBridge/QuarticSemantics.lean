import BulksketchBridge.QuarticSemanticsSpec
import BulksketchBridge.QuarticBatchField
import BulksketchBridge.QuarticControl
import BulksketchBridge.AffineQuartic

namespace BulksketchBridge.QuarticSemantics

open Aeneas Aeneas.Std Algebra.Gf64 bulksketch.backend.contract
open QuarticControl
open AffineQuartic (toField_xorWord nonzero_field nonzero_word)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem square_field (word : U64) :
    toField (squareWord word).bv = toField word.bv ^ 2 := toField_square _

private theorem mul_field (a b : U64) :
    toField (mulWord a b).bv = toField a.bv * toField b.bv := toField_mul _ _

private theorem inverse_field (a : U64) :
    toField (inverseWord a).bv = (toField a.bv)⁻¹ := wordFieldEquiv.apply_symm_apply _

private theorem frobenius_field (word : U64) :
    toField (frobeniusWord word 31#u32).bv = toField word.bv ^ (2 ^ 31 : Nat) :=
  toField_iterateSquare 31 _

private theorem shift_field (a c : U64) (nonzeroA : a ≠ 0#u64) :
    toField a.bv * toField (shiftWord (mulWord c (inverseWord a))).bv ^ 2 = toField c.bv := by
  rw [shiftWord, square_field, frobenius_field, frobenius_field, QuarticReciprocal.shift_squares_to_ratio,
    mul_field, inverse_field]
  field_simp [nonzero_field a nonzeroA]

private theorem denominator_field (b d shift : U64) :
    toField (denominatorWord b d shift).bv =
      QuarticReciprocal.denominator (toField b.bv) (toField d.bv) (toField shift.bv) := by
  simp only [denominatorWord, QuarticReciprocal.denominator, toField_xorWord, square_field, mul_field]
  rw [← pow_mul]

private theorem normalized_value (a b d shift : U64) (z : Field) :
    let (b', c', d') := transformedCoefficients a b shift (inverseWord (denominatorWord b d shift))
    AffineQuartic.evaluate b' c' d' z =
      QuarticReciprocal.reciprocal (toField a.bv) (toField b.bv) (toField d.bv) (toField shift.bv) z := by
  simp only [transformedCoefficients, AffineQuartic.evaluate, QuarticReciprocal.reciprocal,
    mul_field, toField_xorWord, inverse_field, denominator_field]

private theorem array_member (roots : Words) (i : Fin 4) : roots[i.val]! ∈ roots.val := by
  have bounded : i.val < roots.val.length := by simp
  rw [Array.getElem!_Nat_eq, ← List.Inhabited_getElem_eq_getElem! _ _ bounded]
  exact List.getElem_mem bounded

private theorem finish_represented (shift : U64) (roots : Words)
    (nonzero : ∀ word ∈ roots.val, word ≠ 0#u64) :
    ∃ output, finish shift (some roots) = some output ∧
      output.val.map (fun word => toField word.bv) =
        roots.val.map (fun word => (toField word.bv)⁻¹ + toField shift.bv) := by
  have nz (i : Fin 4) : toField roots[i.val]!.bv ≠ 0 :=
    nonzero_field _ (nonzero _ (array_member roots i))
  let total := mulWord (QuarticLoops.prefixes roots)[3]! roots[3]!
  have totalNZ : total ≠ 0#u64 := by
    apply nonzero_word
    exact QuarticLoops.total_product_nonzero roots nz
  refine ⟨QuarticLoops.shiftedReciprocals roots (QuarticLoops.prefixes roots) shift (inverseWord total), ?_, ?_⟩
  · have noZero : 0#u64 ∉ roots.val := fun mem => nonzero _ mem rfl
    have inverseCall : Inverse.expectedFieldInverse total = some (inverseWord total) := by
      simp only [Inverse.expectedFieldInverse, totalNZ, ite_false, DirectTwo.inverseWord]
    simp only [finish, Option.bind_eq_bind, Option.bind_some, noZero, ite_false]
    change (Inverse.expectedFieldInverse total).bind _ = _
    rw [inverseCall]
    rfl
  · exact QuarticLoops.shiftedReciprocals_field_list roots shift (inverseWord total) nz (inverse_field total)

private theorem finish_sound (a b c d shift : U64) (roots output : Words)
    (shiftEq : toField a.bv * toField shift.bv ^ 2 = toField c.bv)
    (denomNZ : QuarticReciprocal.denominator (toField b.bv) (toField d.bv) (toField shift.bv) ≠ 0)
    (distinct : roots.val.Nodup)
    (root : ∀ word ∈ roots.val,
      QuarticReciprocal.reciprocal (toField a.bv) (toField b.bv) (toField d.bv) (toField shift.bv)
        (toField word.bv) = 0)
    (represented : output.val.map (fun word => toField word.bv) =
      roots.val.map (fun word => (toField word.bv)⁻¹ + toField shift.bv)) :
    FourRoots a b c d output := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  constructor
  · apply List.Nodup.of_map (f := fun word : U64 => toField word.bv)
    rw [represented]
    apply List.Nodup.map _ distinct
    intro x y h
    apply U64.bv_eq_imp_eq
    apply toField_injective
    exact inv_injective (add_right_cancel h)
  · intro word mem
    have mapped : toField word.bv ∈ roots.val.map (fun r => (toField r.bv)⁻¹ + toField shift.bv) := by
      rw [← represented]
      exact List.mem_map_of_mem mem
    obtain ⟨r, hr, equal⟩ := List.mem_map.mp mapped
    rw [← equal]
    exact (QuarticReciprocal.reciprocal_root_iff _ _ _ _ _ _ shiftEq denomNZ
      (QuarticReciprocal.reciprocal_nonzero _ _ _ _ _ denomNZ (root r hr))).mp (root r hr)

private theorem affine_meaning {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (b c d : U64) (arithmetic : Cubic.CorrectArithmetic kernels) (output : Option Words)
    (call : bulksketch.decode.deg34.affine_quartic fieldDictionary kernels b c d = .ok output) :
    (∀ roots, output = some roots → AffineQuartic.FourRoots b c d roots) ∧
    ((∃ roots, output = some roots) ↔ c ≠ 0#u64 ∧ AffineQuartic.CertifiedKernel kernels b c ∧
      ∃ z : Field, AffineQuartic.evaluate b c d z = 0) := by
  obtain ⟨expected, executed, sound, complete⟩ := AffineQuartic.affine_quartic_refines kernels b c d arithmetic
  rw [call] at executed
  have same := Result.ok_injective executed
  subst expected
  exact ⟨sound, complete⟩

theorem quartic_refines : ActualQuarticRefines := by
  intro K kernels factor arithmetic length
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  have control := QuarticControl.quartic_refines kernels factor arithmetic length
  dsimp only
  generalize factor[3]! = a at control ⊢
  generalize factor[2]! = b at control ⊢
  generalize factor[1]! = c at control ⊢
  generalize factor[0]! = d at control ⊢
  by_cases aZero : a = 0#u64
  · have prepared : prepare a b c d = some (.direct b c d) := by simp [prepare, aZero]
    rw [prepared] at control
    obtain ⟨output, affineCall, normal⟩ := control
    have meaning := affine_meaning kernels b c d arithmetic output affineCall
    have evalEq (z : Field) : evaluate a b c d z = AffineQuartic.evaluate b c d z := by
      simp only [evaluate, QuarticReciprocal.evaluate, AffineQuartic.evaluate, aZero,
        show toField (0#u64).bv = 0 from toField_zero, zero_mul, add_zero]
    refine ⟨output, normal, ?_, ?_⟩
    · intro roots returned
      simpa only [FourRoots, AffineQuartic.FourRoots, evalEq] using meaning.1 roots returned
    · simpa only [RecoveryGate, prepared, evalEq, and_assoc] using meaning.2
  · let shift := shiftWord (mulWord c (inverseWord a))
    let denom := denominatorWord b d shift
    by_cases denomZero : denom = 0#u64
    · have prepared : prepare a b c d = none := by
        simp only [prepare, aZero, ite_false]
        exact ite_eq_left denomZero
      rw [prepared] at control
      exact ⟨none, control, by simp, by simp [RecoveryGate, prepared]⟩
    · let coefficients := transformedCoefficients a b shift (inverseWord denom)
      have prepared : prepare a b c d = some (.shifted coefficients.1 coefficients.2.1 coefficients.2.2 shift) := by
        simp only [prepare, aZero, ite_false]
        exact ite_eq_right denomZero
      rw [prepared] at control
      obtain ⟨output, affineCall, normal⟩ := control
      have meaning := affine_meaning kernels _ _ _ arithmetic output affineCall
      have shiftEq : toField a.bv * toField shift.bv ^ 2 = toField c.bv := shift_field a c aZero
      have denomNZ : QuarticReciprocal.denominator (toField b.bv) (toField d.bv) (toField shift.bv) ≠ 0 := by
        rw [← denominator_field]
        exact nonzero_field denom denomZero
      have normalized (z : Field) :
          AffineQuartic.evaluate coefficients.1 coefficients.2.1 coefficients.2.2 z =
            QuarticReciprocal.reciprocal (toField a.bv) (toField b.bv) (toField d.bv) (toField shift.bv) z :=
        normalized_value a b d shift z
      have solvable :
          (∃ z : Field, AffineQuartic.evaluate coefficients.1 coefficients.2.1 coefficients.2.2 z = 0) ↔
            ∃ z : Field, evaluate a b c d z = 0 := by
        simp only [normalized, evaluate]
        exact QuarticReciprocal.reciprocal_solvable_iff _ _ _ _ _ shiftEq denomNZ
      have success :
          (∃ roots, output = some roots) ↔ RecoveryGate kernels a b c d ∧
            ∃ z : Field, evaluate a b c d z = 0 := by
        rw [meaning.2, solvable]
        simp only [RecoveryGate, prepared, and_assoc]
      cases output with
      | none => exact ⟨none, normal, by simp, success⟩
      | some roots =>
        have rootsSound := meaning.1 roots rfl
        have reciprocalRoot (word : U64) (mem : word ∈ roots.val) :
            QuarticReciprocal.reciprocal (toField a.bv) (toField b.bv) (toField d.bv) (toField shift.bv)
              (toField word.bv) = 0 := by
          rw [← normalized]
          exact rootsSound.2 word mem
        have nonzero (word : U64) (mem : word ∈ roots.val) : word ≠ 0#u64 :=
          nonzero_word word (QuarticReciprocal.reciprocal_nonzero _ _ _ _ _ denomNZ (reciprocalRoot word mem))
        obtain ⟨updated, finished, represented⟩ := finish_represented shift roots nonzero
        rw [finished] at normal
        refine ⟨some updated, normal, ?_, ?_⟩
        · intro selected returned
          have same := Option.some.inj returned
          subst selected
          exact finish_sound a b c d shift roots updated shiftEq denomNZ rootsSound.1 reciprocalRoot represented
        · exact ⟨fun _ => success.mp ⟨roots, rfl⟩, fun _ => ⟨updated, rfl⟩⟩

end BulksketchBridge.QuarticSemantics
