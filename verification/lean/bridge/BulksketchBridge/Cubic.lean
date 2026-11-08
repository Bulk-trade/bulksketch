import BulksketchBridge.CubicAlgebra
import BulksketchBridge.CubeRoot
import BulksketchBridge.DirectTwoSpec
import BulksketchBridge.InverseUsing
import BulksketchBridge.MapsQuadratic

namespace BulksketchBridge.Cubic

open Aeneas Aeneas.Std Algebra.Gf64 bulksketch.backend.contract bulksketch.decode.deg34

private abbrev mulWord := Inverse.multiplyNativeWord
private noncomputable abbrev inverseWord := DirectTwo.inverseWord

private theorem normalized_equation {target solution : U64}
    (found : MapsQuadratic.expectedSolution target = some solution) :
    Square.expectedWord solution ^^^ solution = target := by
  obtain ⟨output, normal, meaning⟩ := MapsQuadratic.solve_quadratic_exact_meaning target
  rw [MapsQuadratic.solve_quadratic_refines, found] at normal
  have outputEq : output = some solution := (Result.ok_injective normal).symm
  subst output
  apply U64.bv_eq_imp_eq
  exact meaning.1

theorem quadratic_refines : ActualQuadraticHelperReturnsExactOption := by
  intro K kernels square solve target
  have solved : kernels.ArithmeticInst.solve_quadratic target =
      Result.ok (MapsQuadratic.expectedSolution target) :=
    (solve target).trans (MapsQuadratic.solve_quadratic_refines target)
  unfold quadratic
  simp only [solved, bind_ok, bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  cases found : MapsQuadratic.expectedSolution target with
  | none =>
    simp only [bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
  | some solution =>
    have squared : kernels.ArithmeticInst.square solution = Result.ok (Square.expectedWord solution) :=
      (square solution).trans (Square.square_refines solution)
    simp only [squared, bind_ok, lift, normalized_equation found, decide_true, CubeRootRuntime.thenSome,
      ite_true]

private theorem xor_field (left right : U64) :
    toField (left ^^^ right).bv = toField left.bv + toField right.bv := toField_xor _ _

private theorem mul_field (left right : U64) :
    toField (mulWord left right).bv = toField left.bv * toField right.bv := toField_mul _ _

private theorem square_field (word : U64) :
    toField (Square.expectedWord word).bv = toField word.bv ^ 2 := toField_square _

private theorem inverse_field (word : U64) :
    toField (inverseWord word).bv = (toField word.bv)⁻¹ := wordFieldEquiv.apply_symm_apply _

private theorem field_nonzero (word : U64) (nonzero : word ≠ 0#u64) : toField word.bv ≠ 0 := by
  intro zero
  apply nonzero
  apply U64.bv_eq_imp_eq
  apply toField_injective
  exact zero.trans toField_zero.symm

private theorem nonzero_word (word : U64) (nonzero : toField word.bv ≠ 0) : word ≠ 0#u64 := by
  intro zero
  apply nonzero
  rw [zero]
  exact toField_zero

private def words (a u v : U64) : Array U64 3#usize :=
  let ou := mulWord OMEGA u
  let ov := mulWord OMEGA v
  Array.make 3#usize [a ^^^ u ^^^ v, a ^^^ ou ^^^ ov ^^^ v, a ^^^ ou ^^^ u ^^^ ov]

private theorem words_sound (a b c u v : U64)
    (product : toField u.bv * toField v.bv = toField a.bv ^ 2 + toField b.bv)
    (sum : toField u.bv ^ 3 + toField v.bv ^ 3 = toField a.bv * toField b.bv + toField c.bv) :
    ∀ (root : U64), root ∈ (words a u v).val →
      toField root.bv ^ 3 + toField a.bv * toField root.bv ^ 2 +
        toField b.bv * toField root.bv + toField c.bv = 0 := by
  obtain ⟨first, second, third⟩ := cardano_roots (toField a.bv) (toField b.bv) (toField c.bv)
    (toField u.bv) (toField v.bv) product sum
  intro root member
  change root ∈ [a ^^^ u ^^^ v, a ^^^ mulWord OMEGA u ^^^ mulWord OMEGA v ^^^ v,
    a ^^^ mulWord OMEGA u ^^^ u ^^^ mulWord OMEGA v] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa only [xor_field, evaluate] using first
  · simpa only [xor_field, mul_field, evaluate] using second
  · simpa only [xor_field, mul_field, evaluate] using third

private theorem inverse_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (word : U64) (nonzero : word ≠ 0#u64) :
    kernels.ArithmeticInst.inverse word = Result.ok (some (inverseWord word)) := by
  rw [arithmetic.2.1, InverseUsing.inverse_refines]
  simp only [Inverse.expectedFieldInverse, ite_eq_right nonzero, DirectTwo.inverseWord]

/-- The original cubic body terminates under the selected GF64 callbacks.
Every successful result is a root of the original input polynomial. -/
theorem cubic_refines : ActualCubicReturnsOnlyRoots := by
  intro K kernels a b c arithmetic
  have mulNormal (left right : U64) : kernels.ArithmeticInst.mul left right =
      Result.ok (mulWord left right) := (arithmetic.1.1 left right).trans (native_mul_word left right)
  have squareNormal (word : U64) : kernels.ArithmeticInst.square word =
      Result.ok (Square.expectedWord word) := (arithmetic.1.2.1 word).trans (Square.square_refines word)
  let p := Square.expectedWord a ^^^ b
  let q := mulWord a b ^^^ c
  have pEq : Square.expectedWord a ^^^ b = p := rfl
  have qEq : mulWord a b ^^^ c = q := rfl
  have pField : toField p.bv = toField a.bv ^ 2 + toField b.bv := by rw [← pEq, xor_field, square_field]
  have qField : toField q.bv = toField a.bv * toField b.bv + toField c.bv := by rw [← qEq, xor_field, mul_field]
  by_cases qzero : q = 0#u64
  · refine ⟨none, ?_, ?_⟩
    · simp only [cubic, squareNormal, mulNormal, bind_ok, lift, qEq, qzero, ite_true]
    · intro roots impossible
      contradiction
  · let qi := inverseWord q
    have qInv : kernels.ArithmeticInst.inverse q = Result.ok (some qi) := inverse_normal kernels arithmetic q qzero
    let target := mulWord (mulWord (Square.expectedWord p) p) (Square.expectedWord qi)
    have targetEq : mulWord (mulWord (Square.expectedWord p) p) (Square.expectedWord qi) = target := rfl
    have targetField : toField target.bv = toField p.bv ^ 3 * (toField q.bv)⁻¹ ^ 2 := by
      rw [← targetEq, mul_field, mul_field, square_field, square_field, inverse_field, pow_succ _ 2]
    have normalQuad := quadratic_refines kernels arithmetic.1.2.1 arithmetic.2.2 target
    cases found : MapsQuadratic.expectedSolution target with
    | none =>
      refine ⟨none, ?_, ?_⟩
      · simp only [cubic, squareNormal, mulNormal, bind_ok, lift, pEq, qEq, qzero, ite_false, qInv,
          bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch, targetEq, normalQuad, found,
          bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
      · intro roots impossible
        contradiction
    | some z =>
      let t := mulWord q z
      have tEq : mulWord q z = t := rfl
      let w := if t = 0#u64 then q else t
      have select : (if t = 0#u64 then Result.ok q else Result.ok t) = Result.ok w := by
        by_cases zero : t = 0#u64 <;> simp only [w, zero, ite_true, ite_false]
      obtain ⟨cubeResult, cubeNormal, cubeMeaning⟩ := CubeRoot.cube_root_refines kernels w arithmetic.1
      cases cubeResult with
      | none =>
        refine ⟨none, ?_, ?_⟩
        · simp only [cubic, squareNormal, mulNormal, bind_ok, lift, pEq, qEq, qzero, ite_false, qInv,
            bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch, targetEq, normalQuad, found,
            tEq, select, cubeNormal,
            bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
        · intro roots impossible
          contradiction
      | some u =>
        have zEquation := congrArg (fun word : U64 => toField word.bv) (normalized_equation found)
        rw [xor_field, square_field, targetField] at zEquation
        have wField : toField w.bv = if toField q.bv * toField z.bv = 0 then toField q.bv
            else toField q.bv * toField z.bv := by
          have tField : toField t.bv = toField q.bv * toField z.bv := mul_field q z
          by_cases zero : t = 0#u64
          · have fieldZero : toField q.bv * toField z.bv = 0 := by rw [← tField, zero]; exact toField_zero
            simp only [w, zero, fieldZero, ite_true]
          · have fieldNonzero : toField q.bv * toField z.bv ≠ 0 := tField ▸ field_nonzero t zero
            simp only [w, zero, fieldNonzero, ite_false, tField]
        have radicand : toField w.bv ^ 2 + toField q.bv * toField w.bv = toField p.bv ^ 3 := by
          rw [wField]
          exact radicand_law _ _ _ (field_nonzero q qzero) zEquation
        have companion (v : U64) (vField : toField v.bv = toField p.bv * (toField u.bv)⁻¹) :
            ∀ (root : U64), root ∈ (words a u v).val →
              toField root.bv ^ 3 + toField a.bv * toField root.bv ^ 2 +
                toField b.bv * toField root.bv + toField c.bv = 0 := by
          obtain ⟨product, sum⟩ := companion_law _ _ _ _ cubeMeaning.1 cubeMeaning.2.1 radicand
          apply words_sound a b c u v
          · rw [vField, ← pField]; exact product
          · rw [vField, ← qField]; exact sum
        by_cases pzero : p = 0#u64
        · refine ⟨some (words a u 0#u64), ?_, ?_⟩
          · simp only [cubic, squareNormal, mulNormal, bind_ok, lift, pEq, qEq, qzero, ite_false, qInv,
              bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch, targetEq, normalQuad, found,
              tEq, select, cubeNormal]
            simp only [pzero, ite_true, words]
          · intro roots equal root member
            rw [← Option.some.inj equal] at member
            apply companion 0#u64 ?_ root member
            rw [pzero]
            change toField (0 : BitVec 64) = toField (0 : BitVec 64) * (toField u.bv)⁻¹
            simp only [toField_zero, zero_mul]
        · let ui := inverseWord u
          let v := mulWord p ui
          have invU := inverse_normal kernels arithmetic u (nonzero_word u cubeMeaning.1)
          refine ⟨some (words a u v), ?_, ?_⟩
          · simp only [cubic, squareNormal, mulNormal, bind_ok, lift, pEq, qEq, qzero, ite_false, qInv,
              bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch, targetEq, normalQuad, found,
              tEq, select, cubeNormal, pzero, invU, words, v, ui]
          · intro roots equal root member
            rw [← Option.some.inj equal] at member
            apply companion v ?_ root member
            simp only [v, ui, mul_field, inverse_field]

end BulksketchBridge.Cubic
