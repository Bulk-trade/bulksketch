import BulksketchBridge.AffineEnumerationCompleteness
import BulksketchBridge.AffineMultipleAlgebra

namespace BulksketchBridge.RootAffinePreparation

open Aeneas.Std Polynomial Algebra.Gf64 AffineSubspaces AffineSubspaceAlgebra AffineEnumerate
open scoped BigOperators

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

noncomputable def cosetPoints (basis : Slice U64) (base : Field) : Finset Field := by
  classical
  exact (graySegment basis base 0 (2 ^ basis.length)).toFinset

theorem mem_coset_points (basis : Slice U64) (base point : Field) :
    point ∈ cosetPoints basis base ↔ point ∈ coset base (prefixDirections basis basis.length) := by
  classical
  rw [cosetPoints, List.mem_toFinset, gray_coset_membership]
  simp only [graySegment, List.mem_ofFn, Nat.zero_add]
  exact ⟨fun ⟨index, found⟩ => ⟨index.val, index.isLt, found⟩,
    fun ⟨index, bound, found⟩ => ⟨⟨index, bound⟩, found⟩⟩

theorem coset_points_card (basis : Slice U64) (base : Field) (independent : IndependentDirections basis) :
    (cosetPoints basis base).card = 2 ^ basis.length := by
  classical
  unfold cosetPoints
  have distinct : (graySegment basis base 0 (2 ^ basis.length)).Nodup := by
    unfold graySegment
    apply List.nodup_ofFn_ofInjective
    intro left right same
    apply Fin.ext
    simp only [Nat.zero_add] at same
    exact gray_points_distinct basis base independent left.isLt right.isLt same
  rw [List.toFinset_card_of_nodup distinct, graySegment, List.length_ofFn]

theorem multiple_root_solves (factor : Polynomial Field) (constant : U64) (linear : Slice U64)
    (multiple : factor ∣ AffineMultiple.witnessPolynomial constant linear)
    (point : Field) (root : factor.IsRoot point) :
    (rowPolynomial linear).eval point = toField constant.bv := by
  obtain ⟨other, product⟩ := multiple
  have zero : (AffineMultiple.witnessPolynomial constant linear).eval point = 0 := by
    rw [product, eval_mul, show factor.eval point = 0 from root, zero_mul]
  simp only [AffineMultiple.witnessPolynomial, eval_add, eval_C] at zero
  apply sub_eq_zero.mp
  rw [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  exact zero

theorem witness_degree_bound (constant : U64) (linear : Slice U64) :
    (AffineMultiple.witnessPolynomial constant linear).natDegree ≤ 2 ^ (linear.length - 1) := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro index above
  have powerPositive : 0 < 2 ^ (linear.length - 1) := by positivity
  have indexPositive : index ≠ 0 := by omega
  rw [AffineMultiple.witnessPolynomial, coeff_add, coeff_C, ite_eq_right indexPositive, zero_add,
    rowPolynomial, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro power member
  have below := Finset.mem_range.mp member
  have bound : 2 ^ power ≤ 2 ^ (linear.length - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have different : index ≠ 2 ^ power := by omega
  simp [coeff_C_mul, coeff_X_pow, different, Ne.symm different]

theorem witness_nonzero (constant : U64) (linear : Slice U64)
    (hasX : 0 < linear.length) (nonzero : linear[(0 : Nat)]! ≠ 0#u64) :
    AffineMultiple.witnessPolynomial constant linear ≠ 0 := by
  intro zero
  have derivative := AffineMultiple.witness_derivative constant linear hasX
  rw [zero, derivative_zero] at derivative
  have fieldZero := C_eq_zero.mp derivative.symm
  apply nonzero
  apply U64.bv_eq_imp_eq
  exact toField_injective (fieldZero.trans toField_zero.symm)

/-- Both original rank guards accept when the affine witness contains
    every root of the split squarefree factor and the solver gives its full
    independent fiber. This does not assume either guard succeeds. -/
theorem affine_rank_bounds (factor : Polynomial Field) (constant : U64) (linear basis : Slice U64)
    (base : Field) (hasX : 0 < linear.length) (nonzeroX : linear[(0 : Nat)]! ≠ 0#u64)
    (multiple : factor ∣ AffineMultiple.witnessPolynomial constant linear)
    (nonzeroFactor : factor ≠ 0) (split : factor.Splits) (simple : factor.roots.Nodup)
    (independent : IndependentDirections basis)
    (fiber : ∀ point : Field, (rowPolynomial linear).eval point = toField constant.bv ↔
      point ∈ coset base (prefixDirections basis basis.length)) :
    factor.natDegree ≤ 2 ^ basis.length ∧ basis.length < linear.length := by
  classical
  let points := cosetPoints basis base
  let witness := AffineMultiple.witnessPolynomial constant linear
  have card : points.card = 2 ^ basis.length := coset_points_card basis base independent
  have allRoots : factor.roots.toFinset ⊆ points := by
    intro point member
    have root : factor.IsRoot point := (mem_roots nonzeroFactor).mp (Multiset.mem_toFinset.mp member)
    exact (mem_coset_points basis base point).mpr ((fiber point).mp (multiple_root_solves _ _ _ multiple _ root))
  have rootCount := Finset.card_le_card allRoots
  rw [Multiset.toFinset_card_of_nodup simple, ← split.natDegree_eq_card_roots, card] at rootCount
  have witnessNonzero : witness ≠ 0 := witness_nonzero constant linear hasX nonzeroX
  have allPoints : points ⊆ witness.roots.toFinset := by
    intro point member
    have root := (fiber point).mpr ((mem_coset_points basis base point).mp member)
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots witnessNonzero).mpr
    change (AffineMultiple.witnessPolynomial constant linear).eval point = 0
    rw [AffineMultiple.witnessPolynomial, eval_add, eval_C, root, CharTwo.add_self_eq_zero]
  have support : witness.roots.toFinset.card ≤ witness.roots.card := Multiset.toFinset_card_le witness.roots
  have bounded := (Finset.card_le_card allPoints).trans (support.trans (card_roots' witness))
  rw [card] at bounded
  have powBound := bounded.trans (witness_degree_bound constant linear)
  refine ⟨rootCount, ?_⟩
  by_contra! exceeds
  have powerLt := Nat.pow_lt_pow_right (a := 2) (by decide) (show linear.length - 1 < basis.length by omega)
  omega

end BulksketchBridge.RootAffinePreparation
