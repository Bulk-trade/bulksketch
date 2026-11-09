import BulksketchBridge.RootLeaf
import BulksketchBridge.MapsQuadratic
import BulksketchBridge.DenseReducerAlgebra
import Mathlib.Tactic.FieldSimp

namespace BulksketchBridge.RootLeaf

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient SliceKernels
open BulksketchProofs.Field

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem target_value (constant linear : U64) :
    toField (quadraticTarget constant linear).bv =
      toField constant.bv * (toField linear.bv)⁻¹ ^ 2 := by
  unfold quadraticTarget
  change toField (multiplyWord constant.bv (Period.squareWord (DirectTwo.inverseWord linear).bv)) = _
  rw [toField_mul, toField_square]
  change _ * toField (wordFieldEquiv.symm (toField linear.bv)⁻¹) ^ 2 = _
  rw [show toField (wordFieldEquiv.symm (toField linear.bv)⁻¹) = (toField linear.bv)⁻¹
    from wordFieldEquiv.apply_symm_apply _]

private theorem quadratic_value (word : BitVec 64) :
    toField (Maps.quadratic word) = toField word ^ 2 + toField word := by
  rw [Maps.quadratic, toField_xor, toField_square]

private theorem trace_zero_solution (target : U64) (point : Field)
    (equation : point ^ 2 + point = toField target.bv) :
    ∃ solution, MapsQuadratic.expectedSolution target = some solution ∧
      toField solution.bv ^ 2 + toField solution.bv = toField target.bv := by
  have solvable : ∃ word : BitVec 64, Maps.quadratic word = target.bv := by
    refine ⟨wordFieldEquiv.symm point, toField_injective ?_⟩
    rw [quadratic_value]
    rw [show toField (wordFieldEquiv.symm point) = point from wordFieldEquiv.apply_symm_apply _]
    exact equation
  have zero := (Maps.quadratic_solvable_iff_trace_zero target.bv).mp solvable
  have traceBit : Maps.traceBit target.bv = false := by
    cases bit : Maps.traceBit target.bv <;> simp [bit] at zero ⊢
  obtain ⟨output, ran, meaning⟩ := MapsQuadratic.solve_quadratic_exact_meaning target
  have someOutput : output = some (MapsQuadratic.expectedMatrixWord target) := by
    have equality := Result.ok_injective ((MapsQuadratic.solve_quadratic_refines target).symm.trans ran)
    simpa only [MapsQuadratic.expectedSolution, traceBit, Bool.false_eq_true, ite_false] using equality.symm
  subst output
  exact ⟨_, by simp only [MapsQuadratic.expectedSolution, traceBit, Bool.false_eq_true, ite_false],
    (quadratic_value _).symm.trans (congrArg toField meaning.1)⟩

private theorem at_quadratic (words : Slice U64) (width : words.length = 3)
    (monic : words[(2 : Nat)]! = 1#u64) (point : Field) :
    (slicePolynomial words).eval point =
      point ^ 2 + toField words[(1 : Nat)]!.bv * point + toField words[(0 : Nat)]!.bv := by
  have oneValue : toField (1#u64).bv = 1 := toField_one
  simp only [slicePolynomial, width, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, eval_add, eval_monomial, pow_zero, pow_one, mul_one, monic, oneValue, one_mul]
  ring

private theorem nonzero_word (word : U64) (nonzero : toField word.bv ≠ 0) : word ≠ 0#u64 := by
  intro zero
  apply nonzero
  rw [zero]
  exact toField_zero

/-- The actual model used by the degree-two native leaf returns two
distinct nonzero roots and they are exactly the roots of the factor. -/
theorem quadratic_candidates_complete (words : Slice U64) (width : words.length = 3)
    (monic : words[(2 : Nat)]! = 1#u64)
    (split : (slicePolynomial words).Splits) (simple : (slicePolynomial words).roots.Nodup)
    (noZero : ¬ (slicePolynomial words).IsRoot 0) :
    ∃ first second : U64, leafCandidates 2 words = .Ok (twoRoots first second) ∧
      first ≠ second ∧ first ≠ 0#u64 ∧ second ≠ 0#u64 ∧
      ∀ point, (slicePolynomial words).IsRoot point ↔
        point = toField first.bv ∨ point = toField second.bv := by
  classical
  let a := toField words[(0 : Nat)]!.bv
  let b := toField words[(1 : Nat)]!.bv
  let factor := slicePolynomial words
  obtain ⟨factorMonic, factorDegree⟩ := DenseReducerAlgebra.modulus_monic words 2 width monic
  have degree : factor.natDegree = 2 := natDegree_eq_of_degree_eq_some factorDegree
  have size : 1 < factor.roots.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup simple, ← split.natDegree_eq_card_roots, degree]
    decide
  obtain ⟨x, y, hx, hy, different⟩ := Finset.one_lt_card_iff.mp size
  have evalZero (point : Field) (member : point ∈ factor.roots.toFinset) : point ^ 2 + b * point + a = 0 := by
    have root := (mem_roots factorMonic.ne_zero).mp (Multiset.mem_toFinset.mp member)
    rw [← at_quadratic words width monic]
    exact root
  have bNonzero : b ≠ 0 := by
    intro zero
    have left := evalZero x hx
    have right := evalZero y hy
    rw [zero, zero_mul, add_zero] at left right
    have equal : x ^ 2 = y ^ 2 := add_right_cancel (left.trans right.symm)
    have sumZero : (x + y) ^ 2 = 0 := by
      rw [add_sq, ← equal, show (2 : Field) = 0 by exact CharP.cast_eq_zero Field 2, zero_mul,
        zero_mul, add_zero, CharTwo.add_self_eq_zero]
    have same : x + y = 0 := by simpa only [pow_eq_zero_iff (by decide : 2 ≠ 0)] using sumZero
    apply different
    calc
      x = (x + y) + y := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = y := by rw [same, zero_add]
  have xEq : x ^ 2 + b * x = a := by
    have h := congrArg (· + a) (evalZero x hx)
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using h
  let target := quadraticTarget words[0]! words[1]!
  have tgt : toField target.bv = a * b⁻¹ ^ 2 := target_value ..
  have normalized : (x * b⁻¹) ^ 2 + x * b⁻¹ = toField target.bv := by
    rw [tgt, ← xEq]
    field_simp [bNonzero]
  obtain ⟨solution, solved, equation⟩ := trace_zero_solution target (x * b⁻¹) normalized
  let first := Inverse.multiplyNativeWord words[1]! solution
  let second := first ^^^ words[1]!
  let r := toField first.bv
  let s := toField second.bv
  have firstVal : r = b * toField solution.bv := toField_mul ..
  have secondVal : s = r + b := toField_xor ..
  have sum : r + s = b := by rw [secondVal, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have prod : r * s = a := by
    rw [secondVal, firstVal, ← show b ^ 2 * (toField solution.bv ^ 2 + toField solution.bv) =
        b * toField solution.bv * (b * toField solution.bv + b) by ring, equation, tgt]
    field_simp [bNonzero]
  have roots (point : Field) : factor.IsRoot point ↔ point = r ∨ point = s := by
    change factor.eval point = 0 ↔ _
    have eval : factor.eval point = (point + r) * (point + s) := by
      rw [at_quadratic words width monic]
      change point ^ 2 + b * point + a = (point + r) * (point + s)
      rw [← sum, ← prod]
      ring
    rw [eval, mul_eq_zero]
    have eq (p q : Field) : p + q = 0 ↔ p = q := by
      simpa only [sub_eq_add_neg, CharTwo.neg_eq] using (sub_eq_zero : p - q = 0 ↔ p = q)
    rw [eq, eq]
  have distinct : first ≠ second := by
    intro equal
    apply bNonzero
    rw [← sum, show s = r from congrArg (fun w : U64 => toField w.bv) equal.symm, CharTwo.add_self_eq_zero]
  have firstNonzero : first ≠ 0#u64 := nonzero_word first
    (fun zero => noZero ((roots 0).mpr (Or.inl zero.symm)))
  have secondNonzero : second ≠ 0#u64 := nonzero_word second
    (fun zero => noZero ((roots 0).mpr (Or.inr zero.symm)))
  refine ⟨first, second, ?_, distinct, firstNonzero, secondNonzero, roots⟩
  have linearNonzero := nonzero_word words[1]! bNonzero
  unfold leafCandidates
  change MapsQuadratic.expectedSolution (quadraticTarget words[0]! words[1]!) = some solution at solved
  simp only [linearNonzero, ite_false, solved]
  rfl

#print axioms quadratic_candidates_complete

end BulksketchBridge.RootLeaf
