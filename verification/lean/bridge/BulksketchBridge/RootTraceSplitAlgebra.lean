import BulksketchBridge.RootTraceField
import BulksketchBridge.RootTraceProgress
import BulksketchBridge.AffineSplitterEvaluation

namespace BulksketchBridge.RootTrace

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient SliceKernels RebuiltLfsr RootRun

/-- The trace polynomial is idempotent modulo a split factor with distinct
roots. It has degree below the factor and its value is a bit at every root. -/
theorem trace_mod_square_idempotent (factor polynomial : Polynomial Field)
    (monic : factor.Monic) (split : factor.Splits) (simple : factor.roots.Nodup)
    (degree : polynomial.natDegree < factor.natDegree)
    (binary : ∀ point, factor.IsRoot point → polynomial.eval point = 0 ∨ polynomial.eval point = 1) :
    (polynomial ^ 2) %ₘ factor = polynomial := by
  classical
  have nonunit : factor ≠ 1 := by
    intro one
    rw [one, natDegree_one] at degree
    omega
  apply eq_of_natDegree_lt_card_of_eval_eq' _ _ factor.roots.toFinset
  · intro point present
    have root : factor.IsRoot point := (mem_roots monic.ne_zero).mp (Multiset.mem_toFinset.mp present)
    rw [modByMonic_eq_sub_mul_div, eval_sub, eval_mul, show factor.eval point = 0 from root,
      zero_mul, sub_zero, eval_pow]
    rcases binary point root with bit | bit <;> simp [bit]
  · rw [Multiset.toFinset_card_of_nodup simple, ← split.natDegree_eq_card_roots, max_lt_iff]
    exact ⟨natDegree_modByMonic_lt _ monic nonunit, degree⟩

theorem trace_value_binary (modulus trace : Slice U64) (length : Usize) (splitter : U64)
    (invariant : traceInvariant modulus splitter 64 length trace) :
    ∀ point, (slicePolynomial modulus).IsRoot point →
      let value := (slicePolynomial (prefixSlice trace length.val)).eval point
      value = 0 ∨ value = 1 := by
  intro point root
  dsimp only
  rw [invariant point root, trace_at_is_algebra_trace]
  have bit : ∀ value : ZMod 2, value = 0 ∨ value = 1 := by decide
  rcases bit (Algebra.trace (ZMod 2) Field (toField splitter.bv * point)) with zero | one
  · left
    rw [zero, map_zero]
  · right
    rw [one, map_one]

theorem words_eq_of_poly (left right : Slice U64) (width : left.length = right.length)
    (polynomial : slicePolynomial left = slicePolynomial right) : left = right := by
  apply Slice.ext_getElem width
  intro index inLeft inRight
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ inLeft, Slice.Inhabited_getElem_eq_getElem! _ _ inRight]
  have coefficient := congrArg (fun (p : Polynomial Field) => p.coeff index) polynomial
  rw [slicePolynomial_coeff, slicePolynomial_coeff, ite_eq_left inLeft, ite_eq_left inRight] at coefficient
  exact U64.bv_eq_imp_eq _ _ (toField_injective coefficient)

theorem polynomial_of_zero_padding (padded original : Slice U64)
    (count : Nat) (room : count ≤ original.length)
    (value : padded.val = original.val.take count ++ List.replicate (original.length - count) 0#u64) :
    slicePolynomial padded = slicePolynomial (prefixSlice original count) := by
  have len : padded.length = original.length := by
    change padded.val.length = original.length
    rw [value, List.length_append, List.length_take, List.length_replicate, Nat.min_eq_left room]
    omega
  have prefixLen : (prefixSlice original count).length = count := by
    rw [prefix_length, Nat.min_eq_left room]
  ext index
  rw [slicePolynomial_coeff, slicePolynomial_coeff, prefixLen, len]
  by_cases before : index < count
  · have inside : index < original.length := by omega
    simp only [inside, before, ite_true, Slice.getElem!_Nat_eq, value, prefixSlice, Slice.from_val]
    rw [List.getElem!_append_left _ _ _ (by rwa [List.length_take, Nat.min_eq_left room])]
  · rw [ite_eq_right before]
    by_cases inside : index < original.length
    · rw [ite_eq_left inside]
      simp only [Slice.getElem!_Nat_eq, value]
      rw [List.getElem!_append_right _ _ _ (by rw [List.length_take, Nat.min_eq_left room]; omega)]
      rw [List.length_take, Nat.min_eq_left room, List.getElem!_replicate _ (by omega)]
      exact toField_zero
    · exact ite_eq_right inside

#print axioms trace_mod_square_idempotent
#print axioms polynomial_of_zero_padding

end BulksketchBridge.RootTrace
