import BulksketchBridge.AffineQuarticSpec
import BulksketchBridge.Cubic
import BulksketchBridge.Algebra.WordSquare
import Mathlib.Algebra.CharP.Algebra

namespace BulksketchBridge.AffineQuartic

open Aeneas.Std Algebra.Gf64

set_option maxRecDepth 2048

theorem toField_xorWord (left right : U64) :
    toField (left ^^^ right).bv = toField left.bv + toField right.bv := toField_xor _ _

private theorem toField_mulWord (left right : U64) :
    toField (mulWord left right).bv = toField left.bv * toField right.bv :=
  toField_mul _ _

private theorem toField_squareWord (word : U64) :
    toField (squareWord word).bv = toField word.bv ^ 2 := toField_square _

private theorem toField_inverseWord (word : U64) :
    toField (inverseWord word).bv = (toField word.bv)⁻¹ := wordFieldEquiv.apply_symm_apply _

theorem nonzero_field (word : U64) (nonzero : word ≠ 0#u64) : toField word.bv ≠ 0 := by
  intro zero
  apply nonzero
  apply U64.bv_eq_imp_eq
  apply toField_injective
  exact zero.trans toField_zero.symm

theorem nonzero_word (word : U64) (nonzero : toField word.bv ≠ 0) : word ≠ 0#u64 := by
  intro zero
  apply nonzero
  rw [zero]
  exact toField_zero

private theorem chosen_equation (target solution : U64)
    (found : MapsQuadratic.expectedSolution target = some solution) :
    toField solution.bv ^ 2 + toField solution.bv = toField target.bv := by
  have h := congrArg (fun word : U64 => toField word.bv) (Cubic.normalized_equation found)
  simpa only [toField_xorWord, toField_squareWord] using h

private theorem choose_exists (target : U64)
    (solvable : ∃ solution : Field, solution ^ 2 + solution = toField target.bv) :
    ∃ solution, MapsQuadratic.expectedSolution target = some solution := by
  obtain ⟨solution, equation⟩ := solvable
  obtain ⟨bits, value⟩ := toField_surjective solution
  have word : BulksketchProofs.Field.Maps.quadratic bits = target.bv := by
    apply toField_injective
    rw [BulksketchProofs.Field.Maps.quadratic, toField_xor, toField_square, value, equation]
  have trace := BulksketchProofs.Field.Maps.quadratic_trace_zero bits
  rw [word] at trace
  exact ⟨MapsQuadratic.expectedMatrixWord target, by simp [MapsQuadratic.expectedSolution, trace]⟩

private theorem toField_scaledTarget (other c target : U64) :
    toField (scaledTarget other (inverseWord c) target).bv =
      toField target.bv * (toField other.bv * (toField c.bv)⁻¹) ^ 2 := by
  rw [scaledTarget, toField_mulWord, toField_squareWord, toField_mulWord, toField_inverseWord]

private theorem scaled_choice_exists (a other c target : U64)
    (nonzero : toField a.bv ≠ 0)
    (reciprocal : toField other.bv * (toField c.bv)⁻¹ = (toField a.bv)⁻¹)
    (solvable : ∃ z, quadratic (toField a.bv) z = toField target.bv) :
    ∃ solution, MapsQuadratic.expectedSolution (scaledTarget other (inverseWord c) target) = some solution := by
  apply choose_exists
  rw [toField_scaledTarget, reciprocal]
  exact normalized_exists _ _ nonzero solvable

private theorem scaled_choice_root (a other c target solution : U64)
    (nonzero : toField a.bv ≠ 0)
    (reciprocal : toField other.bv * (toField c.bv)⁻¹ = (toField a.bv)⁻¹)
    (found : MapsQuadratic.expectedSolution (scaledTarget other (inverseWord c) target) = some solution) :
    quadratic (toField a.bv) (toField (mulWord a solution).bv) = toField target.bv := by
  have eq := chosen_equation _ _ found
  rw [toField_scaledTarget, reciprocal] at eq
  rw [toField_mulWord]
  exact scaled_quadratic _ _ _ nonzero eq

private theorem eval_eq (b c d u v : U64)
    (coefB : toField b.bv = toField v.bv + toField u.bv ^ 2)
    (coefC : toField u.bv * toField v.bv = toField c.bv) (z : Field) :
    evaluate b c d z = quartic (toField u.bv) (toField v.bv) (toField d.bv) z := by
  rw [evaluate, quartic, coefB, coefC]

theorem fiber_choices_refine (b c d u v : U64)
    (uNZ : toField u.bv ≠ 0) (vNZ : toField v.bv ≠ 0)
    (coefB : toField b.bv = toField v.bv + toField u.bv ^ 2)
    (coefC : toField u.bv * toField v.bv = toField c.bv)
    (kernel : ∃ r, quadratic (toField u.bv) r = toField v.bv) :
    (∀ roots, fiberChoices u v c d = some roots → FourRoots b c d roots) ∧
    ((∃ roots, fiberChoices u v c d = some roots) ↔ ∃ z : Field, evaluate b c d z = 0) := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  obtain ⟨uInv, vInv⟩ := inverse_scales _ _ _ uNZ vNZ coefC
  have sound : ∀ roots, fiberChoices u v c d = some roots → FourRoots b c d roots := by
    intro roots found
    simp only [fiberChoices, Option.bind_eq_bind] at found
    rw [Option.bind_eq_some_iff] at found
    obtain ⟨outer, outerFound, found⟩ := found
    rw [Option.bind_eq_some_iff] at found
    obtain ⟨first, firstFound, found⟩ := found
    rw [Option.bind_eq_some_iff] at found
    obtain ⟨second, secondFound, found⟩ := found
    have wRoot := scaled_choice_root v u c d outer vNZ vInv outerFound
    have xRoot := scaled_choice_root u v c (mulWord v outer) first uNZ uInv firstFound
    have yRoot := scaled_choice_root u v c (mulWord v outer ^^^ v) second uNZ uInv secondFound
    rw [toField_xorWord] at yRoot
    let x := mulWord u first
    let y := mulWord u second
    have result : roots = Array.make 4#usize [x, x ^^^ u, y, y ^^^ u] := (Option.some.inj found).symm
    rw [result]
    obtain ⟨solves, distinct⟩ := affine_four_roots _ _ _ _ _ _ uNZ vNZ wRoot xRoot yRoot
    change List.Nodup [x, x ^^^ u, y, y ^^^ u] ∧
      ∀ word ∈ [x, x ^^^ u, y, y ^^^ u], evaluate b c d (toField word.bv) = 0
    have mapped : [x, x ^^^ u, y, y ^^^ u].map (fun word => toField word.bv) =
        [toField x.bv, toField x.bv + toField u.bv, toField y.bv, toField y.bv + toField u.bv] := by
      simp only [List.map_cons, List.map_nil, toField_xorWord]
    constructor
    · apply List.Nodup.of_map (f := fun word : U64 => toField word.bv)
      rwa [mapped]
    · intro word member
      rw [eval_eq b c d u v coefB coefC]
      apply solves
      rw [← mapped]
      exact List.mem_map_of_mem member
  refine ⟨sound, ?_, ?_⟩
  · rintro ⟨roots, found⟩
    have length : roots.val.length = 4 := by simp
    have member : roots.val[0] ∈ roots.val := List.getElem_mem (by omega)
    exact ⟨toField roots.val[0].bv, (sound roots found).2 _ member⟩
  · rintro ⟨z, root⟩
    have affineRoot : quartic (toField u.bv) (toField v.bv) (toField d.bv) z = 0 := by
      rwa [eval_eq b c d u v coefB coefC] at root
    have quadraticRoot : quadratic (toField v.bv) (quadratic (toField u.bv) z) = toField d.bv := by
      rw [quartic_composition] at affineRoot
      apply add_right_cancel (b := toField d.bv)
      rw [affineRoot, CharTwo.add_self_eq_zero]
    obtain ⟨outer, outerFound⟩ := scaled_choice_exists v u c d vNZ vInv ⟨_, quadraticRoot⟩
    let w := mulWord v outer
    have wRoot := scaled_choice_root v u c d outer vNZ vInv outerFound
    obtain ⟨firstSolvable, secondSolvable⟩ :=
      solve_both_fibers _ _ _ _ kernel ⟨z, affineRoot⟩ wRoot
    obtain ⟨first, firstFound⟩ := scaled_choice_exists u v c w uNZ uInv firstSolvable
    obtain ⟨second, secondFound⟩ := scaled_choice_exists u v c (w ^^^ v) uNZ uInv
      (by rw [toField_xorWord]; exact secondSolvable)
    refine ⟨Array.make 4#usize [mulWord u first, mulWord u first ^^^ u,
      mulWord u second, mulWord u second ^^^ u], ?_⟩
    simp [fiberChoices, outerFound, firstFound, secondFound, w]

end BulksketchBridge.AffineQuartic
