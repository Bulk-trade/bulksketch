import BulksketchBridge.RootLeafQuadratic
import BulksketchBridge.RootPendingFactors

namespace BulksketchBridge.RootLeaf

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient RebuiltLfsr SliceKernels RootRun
open bulksketch.decode.roots bulksketch.decode.scratch

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

private theorem represented_zero (word : U64) : toField word.bv = 0 ↔ word = 0#u64 := by
  constructor
  · intro zero
    exact U64.bv_eq_imp_eq _ _ (toField_injective (zero.trans toField_zero.symm))
  · intro zero
    rw [zero]
    exact toField_zero

private theorem prefix_read (words : Slice U64) (count index : Nat) (active : index < count) :
    (prefixSlice words count)[index]! = words[index]! := by
  simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD,
    List.getElem?_take_of_lt active]

private theorem linear_eval (words : Slice U64) (width : words.length = 2)
    (monic : words[(1 : Nat)]! = 1#u64) (point : Field) :
    (slicePolynomial words).eval point = point + toField words[(0 : Nat)]!.bv := by
  have oneValue : toField (1#u64).bv = 1 := toField_one
  simp only [slicePolynomial, width, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, eval_add, eval_monomial, pow_zero, pow_one, mul_one, monic, oneValue, one_mul]
  exact add_comm _ _

/-- The exact model used by the original degree-zero, -one and -two leaf
    gives the expected number of distinct nonzero roots and all live roots
    of a positive-degree admitted factor. -/
theorem leaf_candidates_complete (roots : Roots) (workspace : RowWorkspace)
    (degreeBound : roots.degree.val ≤ 2)
    (admitted : 0 < roots.degree.val →
      roots.degree.val < workspace.polynomials.length ∧
      workspace.polynomials[roots.degree.val]! = 1#u64 ∧
      (activeFactor roots workspace).Splits ∧ (activeFactor roots workspace).roots.Nodup ∧
      ¬ (activeFactor roots workspace).IsRoot 0) :
    ∃ words : Slice U64,
      leafCandidates roots.degree.val workspace.polynomials = .Ok words ∧
      words.length = roots.degree.val ∧ 0#u64 ∉ words.val ∧ words.val.Nodup ∧
      (0 < roots.degree.val → ∀ point, (activeFactor roots workspace).IsRoot point ↔
        ∃ word ∈ words.val, point = toField word.bv) := by
  by_cases zero : roots.degree.val = 0
  · refine ⟨emptyRoots, ?_, by simp [emptyRoots, Slice.length, zero], by simp [emptyRoots],
      by simp [emptyRoots], fun positive => (by omega : False).elim⟩
    rw [zero]
    rfl
  have positive : 0 < roots.degree.val := by omega
  obtain ⟨room, lead, split, simple, noZero⟩ := admitted positive
  let coefficients := prefixSlice workspace.polynomials (roots.degree.val + 1)
  have length : coefficients.length = roots.degree.val + 1 := by
    rw [prefix_length, Nat.min_eq_left (by omega)]
  by_cases one : roots.degree.val = 1
  · let word := workspace.polynomials[0]!
    have monic : coefficients[(1 : Nat)]! = 1#u64 := by
      rw [prefix_read _ _ _ (by omega)]
      simpa only [one] using lead
    have meaning (point : Field) : (activeFactor roots workspace).IsRoot point ↔ point = toField word.bv := by
      change (slicePolynomial coefficients).eval point = 0 ↔ _
      rw [linear_eval coefficients (by omega) monic, prefix_read _ _ _ (by omega)]
      simpa only [sub_eq_add_neg, CharTwo.neg_eq] using (sub_eq_zero : point - toField word.bv = 0 ↔ _)
    have nonzero : word ≠ 0#u64 := by
      intro zeroWord
      exact noZero ((meaning 0).mpr ((represented_zero word).mpr zeroWord).symm)
    refine ⟨oneRoot word, ?_, by simp [oneRoot, Slice.length, one], by change 0#u64 ∉ [word]; simpa only [List.mem_singleton] using Ne.symm nonzero,
      by simp [oneRoot], fun _ point => ?_⟩
    · rw [one]
      rfl
    · rw [meaning]
      simp only [oneRoot, Slice.from_val, List.mem_singleton, exists_eq_left]
  · have two : roots.degree.val = 2 := by omega
    have monic : coefficients[(2 : Nat)]! = 1#u64 := by
      rw [prefix_read _ _ _ (by omega)]
      simpa only [two] using lead
    obtain ⟨first, second, evaluated, distinct, firstNonzero, secondNonzero, exactRoots⟩ :=
      quadratic_candidates_complete coefficients (by omega) monic split simple noZero
    have same : leafCandidates 2 workspace.polynomials = leafCandidates 2 coefficients := by
      unfold leafCandidates
      rw [prefix_read _ _ _ (by omega), prefix_read _ _ _ (by omega)]
    refine ⟨twoRoots first second, by rw [two, same, evaluated], ?_, ?_, ?_, ?_⟩
    · rw [two]
      rfl
    · change 0#u64 ∉ [first, second]
      simp [Ne.symm firstNonzero, Ne.symm secondNonzero]
    · change [first, second].Nodup
      simp [distinct]
    · intro _ point
      change (slicePolynomial coefficients).IsRoot point ↔ ∃ word ∈ [first, second], point = toField word.bv
      rw [exactRoots point]
      constructor
      · rintro (atFirst | atSecond)
        · exact ⟨first, by simp, atFirst⟩
        · exact ⟨second, by simp, atSecond⟩
      · rintro ⟨word, present, exactPoint⟩
        rcases (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using present :
          word = first ∨ word = second) with same | same
        · exact Or.inl (same ▸ exactPoint)
        · exact Or.inr (same ▸ exactPoint)

#print axioms leaf_candidates_complete

end BulksketchBridge.RootLeaf
